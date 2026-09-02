const { version } = require("./package.json");
const axios = require('axios');
const crypto = require('crypto');
const cheerio = require('cheerio');
const yts = require('yt-search');
const { File } = require('megajs');
const express = require('express');
const app = express();
const port = process.env.PORT || 3000;

const fs = require('fs-extra');
const path = require('path');
const { promisify } = require('util');
const os = require('os');
const { exec } = require('child_process');
const execAsync = promisify(exec);
const pino = require('pino');
const moment = require('moment-timezone');
const fetch = (...args) =>
  import("node-fetch").then(({ default: fetch }) => fetch(...args));

const {
  default: makeWASocket,
  getAggregateVotesInPollMessage,
  useMultiFileAuthState,
  DisconnectReason,
  getDevice,
  fetchLatestBaileysVersion,
  jidNormalizedUser,
  getContentType,
  Browsers,
  makeInMemoryStore,
  makeCacheableSignalKeyStore,
  downloadContentFromMessage,
  generateWAMessageFromContent,
  prepareWAMessageMedia,
  generateForwardMessageContent,
  proto,
} = require("manaofc-baileys");

const getGroupAdmins = (participants) => {
    var admins = []
    for (let i of participants) {
        i.admin !== null ? admins.push(i.id) : ''
    }
    return admins
}

const runtime = (seconds) => {
seconds = Number(seconds)
var d = Math.floor(seconds / (3600 * 24))
var h = Math.floor(seconds % (3600 * 24) / 3600)
var m = Math.floor(seconds % 3600 / 60)
var s = Math.floor(seconds % 60)
var dDisplay = d > 0 ? d + (d == 1 ? ' day, ' : ' days, ') : ''
var hDisplay = h > 0 ? h + (h == 1 ? ' hour, ' : ' hours, ') : ''
var mDisplay = m > 0 ? m + (m == 1 ? ' minute, ' : ' minutes, ') : ''
var sDisplay = s > 0 ? s + (s == 1 ? ' second' : ' seconds') : ''
return dDisplay + hDisplay + mDisplay + sDisplay;
}

const delay = (ms) => new Promise(resolve => setTimeout(resolve, ms));

function getSriLankaTimestamp() {
    return moment().tz('Asia/Colombo').format('YYYY-MM-DD HH:mm:ss');
}

const config = Object.assign({}, require("./config"), process.env);

// Environment & runtime helpers
const usePairingCode = process.env.PAIRING_CODE === 'true';
function restart() {
    console.log("Restarting bot...");
    process.exit(1);
}



//===================SESSION============================
const sessionPath = path.join(__dirname, "file", "session")

if (!fs.existsSync(path.join(sessionPath, 'creds.json'))) {
  if (config.SESSION_ID) {
    const sessdata = config.SESSION_ID;
    const filer = File.fromURL(`https://mega.nz/file/${sessdata}`);
    filer.download((err, data) => {
      if (err) {
        console.error("Session download error:", err);
        return;
      }
      fs.writeFileSync(path.join(sessionPath, 'creds.json'), data);
      console.log("💕Session Download Completed.💕");
      console.log("⚡Please Wait 5-10 Minutes For Run.⚡");
    });
  }
}

// Anti-delete message store (keep last 500 messages per manaofc)
const messageStore = new Map();
const MAX_STORED_MESSAGES = 500;

function storeMessage(key, message) {
    const jid = key.remoteJid;
    if (!messageStore.has(jid)) {
        messageStore.set(jid, new Map());
    }
    const chatStore = messageStore.get(jid);
    chatStore.set(key.id, {
        message: message,
        timestamp: Date.now(),
        key: key
    });

    if (chatStore.size > MAX_STORED_MESSAGES) {
        const oldestKey = chatStore.keys().next().value;
        chatStore.delete(oldestKey);
    }
}

function getStoredMessage(key) {
    const jid = key.remoteJid;
    const chatStore = messageStore.get(jid);
    if (chatStore && chatStore.has(key.id)) {
        return chatStore.get(key.id);
    }
    return null;
}

function deleteStoredMessage(key) {
    const jid = key.remoteJid;
    const chatStore = messageStore.get(jid);
    if (chatStore) {
        chatStore.delete(key.id);
    }
}

// ========== LID -> REAL NUMBER RESOLVER ==========
async function resolveRealNumber(manaofc, jid, messageKey, chatJid) {
    try {
        const alt = (messageKey && (messageKey.senderPn || messageKey.participantAlt || messageKey.remoteJidAlt)) || null;
        if (alt && !alt.endsWith('@lid')) {
            return '+' + alt.split('@')[0].split(':')[0];
        }

        if (!jid) return 'Unknown';
        const cleanJid = jidNormalizedUser(jid);
        const user = cleanJid.split('@')[0].split(':')[0];
        const isLid = cleanJid.endsWith('@lid');

        if (isLid) {
            try {
                const pn = await manaofc.signalRepository.lidMapping.getPNForLID(cleanJid);
                if (pn) return '+' + jidNormalizedUser(pn).split('@')[0].split(':')[0];
            } catch (e) { }

            if (chatJid && chatJid.endsWith('@g.us')) {
                try {
                    const metadata = await manaofc.groupMetadata(chatJid);
                    const match = (metadata.participants || []).find(p =>
                        (p.id && jidNormalizedUser(p.id) === cleanJid) ||
                        (p.lid && jidNormalizedUser(p.lid) === cleanJid)
                    );
                    const pnJid = match && (match.phoneNumber || match.pn);
                    if (pnJid) return '+' + pnJid.split('@')[0].split(':')[0];
                } catch (e) { }
            }
        }

        if (/^\d{10,}$/.test(user)) {
            return '+' + user;
        }

        return user;
    } catch (e) {
        const fallback = (jid || 'Unknown').split('@')[0].split(':')[0];
        if (/^\d{10,}$/.test(fallback)) {
            return '+' + fallback;
        }
        return fallback;
    }
}

// ========== ANTICALL HELPERS ==========
async function handleAntiCall(manaofc, json, config) {
    if (config.ANTICALL !== 'true') return;

    try {
        const callerId = json[0][2][0][1].from;
        const callId = json[0][2][0][1].id;
        const callStatus = json[0][2][0][2][0][1];

        if (callStatus === 'offer') {
            await manaofc.rejectCall(callId, callerId);

            const anticallMsg = config.ANTICALL_MSG || config.ANTICALL_MSG;
            await manaofc.sendMessage(callerId, { 
                text: "> _*Powered By Manaofc*_ ⚡\n\n*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n📵 *Anti-Call Activated*\n*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n" + anticallMsg + "\n\n⏰ " + getSriLankaTimestamp()
            });

            const botUserJid = jidNormalizedUser(manaofc.user.id);
            const callerNumber = await resolveRealNumber(manaofc, callerId);
            if (botUserJid) {
                await manaofc.sendMessage(botUserJid, {
                    text: "> _*Powered By Manaofc*_ ⚡\n\n*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n🚨 *Call Blocked!*\n📞 *Caller Number:* " + callerNumber + "\n⏰ Time: " + getSriLankaTimestamp() + "\n*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n_Call was automatically rejected._"
                });
            }

            console.log("Anti-call: Blocked call from " + callerId);
        }
    } catch (error) {
        console.error('Anti-call handler error:', error);
    }
}


// ========== STATUS HANDLERS ==========
function setupStatusHandlers(manaofc, config) {
    let lastStatusInteraction = 0;
    const STATUS_INTERACTION_COOLDOWN = 10000;

    manaofc.ev.on('messages.upsert', async ({ messages }) => {
        const message = messages[0];

        if (
            !message?.key ||
            message.key.remoteJid !== 'status@broadcast' ||
            !message.key.participant
        ) {
            return;
        }

        const now = Date.now();

        if (now - lastStatusInteraction < STATUS_INTERACTION_COOLDOWN) {
            return;
        }

        try {
            const from = message.key.remoteJid;
            const presence = config.PRESENCE;

            if (presence) {
                if (presence === "composing") {
                    await manaofc.sendPresenceUpdate("composing", from);
                } else if (presence === "recording") {
                    await manaofc.sendPresenceUpdate("recording", from);
                } else if (presence === "unavailable") {
                    await manaofc.sendPresenceUpdate("unavailable", from);
                } else {
                    await manaofc.sendPresenceUpdate("available", from);
                }
                console.log(`Set ${presence} presence for ${from}`);
            }

            if (config.AUTO_VIEW_STATUS === 'true') {
                let retries = parseInt(config.MAX_RETRIES) || 3;
                while (retries > 0) {
                    try {
                        await manaofc.readMessages([message.key]);
                        console.log(`Viewed status from ${message.key.participant}`);
                        break;
                    } catch (error) {
                        retries--;
                        console.warn(`Failed to read status, retries left: ${retries}`, error);
                        if (retries === 0) throw error;
                        await delay(1000 * ((parseInt(config.MAX_RETRIES) || 3) - retries));
                    }
                }
            }

            if (config.AUTO_LIKE_STATUS === 'true') {
                const emojis = Array.isArray(config.AUTO_LIKE_EMOJI)
                    ? config.AUTO_LIKE_EMOJI
                    : config.AUTO_LIKE_EMOJI;

                const randomEmoji = emojis[Math.floor(Math.random() * emojis.length)];
                let retries = parseInt(config.MAX_RETRIES) || 3;

                while (retries > 0) {
                    try {
                        await manaofc.sendMessage(
                            from,
                            {
                                react: {
                                    text: randomEmoji,
                                    key: message.key,
                                },
                            },
                            {
                                statusJidList: [message.key.participant],
                            }
                        );
                        lastStatusInteraction = now;
                        console.log(`Reacted to status with ${randomEmoji}`);
                        break;
                    } catch (error) {
                        retries--;
                        console.warn(`Failed to react to status, retries left: ${retries}`, error);
                        if (retries === 0) throw error;
                        await delay(1000 * ((parseInt(config.MAX_RETRIES) || 3) - retries));
                    }
                }
            }
        } catch (error) {
            console.error("Status handler error:", error);
        }
    });
}

// ========== ANTIDELETE HANDLER ==========
function setupAntiDeleteHandler(manaofc, config) {
    if (config.ANTIDELETE !== 'true') return;

    manaofc.ev.on('messages.upsert', async ({ messages }) => {
        for (const message of messages) {
            if (!message.key || !message.message) continue;
            if (message.key.remoteJid === 'status@broadcast') continue;

            try {
                storeMessage(message.key, message);
            } catch (error) {
                console.error('Anti-delete store error:', error);
            }
        }
    });

    manaofc.ev.on('messages.update', async (updates) => {
        for (const update of updates) {
            try {
                const { key, update: updateData } = update;

                if (updateData && updateData.message === null) {
                    const storedMsg = getStoredMessage(key);

                    if (storedMsg) {
                        const storedKey = storedMsg.key || key;
                        const senderJid = storedKey.participant || storedKey.remoteJid || key.participant || key.remoteJid;
                        const deletedBy = key.fromMe ? 'You' : await resolveRealNumber(manaofc, senderJid, storedKey, key.remoteJid);
                        const chatJid = key.remoteJid;
                        const isGroup = chatJid.endsWith('@g.us');

                        const botUserJid = jidNormalizedUser(manaofc.user.id);
                        const deletedByNumber = key.fromMe ? 'You' : await resolveRealNumber(manaofc, senderJid, storedKey, key.remoteJid);
                        if (botUserJid) {
                            let notifyText = "> _*Powered By Manaofc*_ ⚡\n\n";
                            notifyText += "*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n";
                            notifyText += "🗑️ *Anti-Delete Alert!*\n\n";
                            notifyText += "👤 *Deleted By Number:* " + deletedByNumber + "\n";
                            notifyText += "💬 *Chat:* " + (isGroup ? 'Group' : 'Private') + "\n";
                            notifyText += "⏰ *Time:* " + getSriLankaTimestamp() + "\n";
                            notifyText += "*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n";
                            notifyText += "📩 *Deleted Message:*\n";

                            const msg = storedMsg.message;
                            const msgType = getContentType(msg.message);

                            if (msgType === 'conversation') {
                                notifyText += "```" + msg.message.conversation + "```";
                            } else if (msgType === 'extendedTextMessage') {
                                notifyText += "```" + msg.message.extendedTextMessage.text + "```";
                            } else if (msgType === 'imageMessage') {
                                notifyText += "[Image] " + (msg.message.imageMessage.caption || '');
                            } else if (msgType === 'videoMessage') {
                                notifyText += "[Video] " + (msg.message.videoMessage.caption || '');
                            } else if (msgType === 'audioMessage') {
                                notifyText += "[Audio/Voice Message]";
                            } else if (msgType === 'documentMessage') {
                                notifyText += "[Document] " + (msg.message.documentMessage.fileName || '');
                            } else if (msgType === 'stickerMessage') {
                                notifyText += "[Sticker]";
                            } else {
                                notifyText += "[" + msgType + "]";
                            }

                            notifyText += "\n\n> _Message recovered by Anti-Delete_";

                            await manaofc.sendMessage(botUserJid, { text: notifyText });

                            try {
                                if (msgType === 'imageMessage' && msg.message.imageMessage.url) {
                                    const buffer = await downloadContentFromMessage(msg.message.imageMessage, 'image');
                                    let chunks = [];
                                    for await (const chunk of buffer) { chunks.push(chunk); }
                                    const imageBuffer = Buffer.concat(chunks);
                                    await manaofc.sendMessage(botUserJid, {
                                        image: imageBuffer,
                                        caption: "> _*Powered By Manaofc*_ ⚡\n\n🗑️ *Deleted Image*\nFrom Number: " + deletedBy + "\nTime: " + getSriLankaTimestamp()
                                    });
                                } else if (msgType === 'videoMessage' && msg.message.videoMessage.url) {
                                    const buffer = await downloadContentFromMessage(msg.message.videoMessage, 'video');
                                    let chunks = [];
                                    for await (const chunk of buffer) { chunks.push(chunk); }
                                    const videoBuffer = Buffer.concat(chunks);
                                    await manaofc.sendMessage(botUserJid, {
                                        video: videoBuffer,
                                        caption: "> _*Powered By Manaofc*_ ⚡\n\n🗑️ *Deleted Video*\nFrom Number: " + deletedBy + "\nTime: " + getSriLankaTimestamp()
                                    });
                                } else if (msgType === 'audioMessage' && msg.message.audioMessage.url) {
                                    const buffer = await downloadContentFromMessage(msg.message.audioMessage, 'audio');
                                    let chunks = [];
                                    for await (const chunk of buffer) { chunks.push(chunk); }
                                    const audioBuffer = Buffer.concat(chunks);
                                    await manaofc.sendMessage(botUserJid, {
                                        audio: audioBuffer,
                                        mimetype: 'audio/mp4',
                                        ptt: msg.message.audioMessage.ptt || false
                                    });
                                } else if (msgType === 'stickerMessage' && msg.message.stickerMessage.url) {
                                    const buffer = await downloadContentFromMessage(msg.message.stickerMessage, 'sticker');
                                    let chunks = [];
                                    for await (const chunk of buffer) { chunks.push(chunk); }
                                    const stickerBuffer = Buffer.concat(chunks);
                                    await manaofc.sendMessage(botUserJid, {
                                        sticker: stickerBuffer
                                    });
                                }
                            } catch (mediaError) {
                                console.error('Failed to resend deleted media:', mediaError);
                            }
                        }

                        deleteStoredMessage(key);
                    }
                }
            } catch (error) {
                console.error('Anti-delete handler error:', error);
            }
        }
    });
}

// ========== ANTICALL HANDLER ==========
function setupAntiCallHandler(manaofc, config) {
    if (config.ANTICALL !== 'true') return;

    manaofc.ws.on('CB:call', async (json) => {
        await handleAntiCall(manaofc, json, config);
    });

    manaofc.ev.on('call', async (calls) => {
        for (const call of calls) {
            try {
                if (call.status === 'offer') {
                    await manaofc.rejectCall(call.id, call.from);

                    const anticallMsg = config.ANTICALL_MSG || config.ANTICALL_MSG;
                    await manaofc.sendMessage(call.from, { 
                        text: "> _*Powered By Manaofc*_ ⚡\n\n*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n📵 *Anti-Call Activated*\n*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n" + anticallMsg + "\n\n⏰ " + getSriLankaTimestamp()
                    });

                    const botUserJid = jidNormalizedUser(manaofc.user.id);
                    const callerNumber2 = await resolveRealNumber(manaofc, call.from);
                    if (botUserJid) {
                        await manaofc.sendMessage(botUserJid, {
                            text: "> _*Powered By Manaofc*_ ⚡\n\n🚨 *Call Blocked!*\n\n📞 *Caller Number:* " + callerNumber2 + "\n⏰ Time: " + getSriLankaTimestamp() + "\n\n_Call was automatically rejected._"
                        });
                    }

                    console.log("Anti-call: Blocked call from " + call.from);
                }
            } catch (error) {
                console.error('Anti-call handler error:', error);
            }
        }
    });
}

// ========== AUTO STATUS SAVER ==========
function setupAutoStatusSaver(manaofc, config) {
    if (config.AUTO_STATUS_SAVER !== 'true') return;

    manaofc.ev.on('messages.upsert', async ({ messages }) => {
        const message = messages[0];
        if (!message?.key || message.key.remoteJid !== 'status@broadcast' || !message.key.participant) return;

        try {
            const botUserJid = jidNormalizedUser(manaofc.user.id);
            if (!botUserJid) return;

            const msgType = getContentType(message.message);
            const sender = await resolveRealNumber(manaofc, message.key.participant, message.key, message.key.remoteJid);
            const caption = "> _*Powered By Manaofc*_ ⚡\n\n*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n💾 *Auto Status Saved*\n👤 *From:* " + sender + "\n📂 *Type:* " + (msgType?.replace('Message', '') || 'Unknown') + "\n⏰ *Time:* " + getSriLankaTimestamp() + "\n*╰━━━━━━━✧༺♥༻✧━━━━━━━*";

            if (msgType === 'imageMessage') {
                const buffer = await downloadContentFromMessage(message.message.imageMessage, 'image');
                let chunks = [];
                for await (const chunk of buffer) chunks.push(chunk);
                await manaofc.sendMessage(botUserJid, {
                    image: Buffer.concat(chunks),
                    caption: caption
                });
            } else if (msgType === 'videoMessage') {
                const buffer = await downloadContentFromMessage(message.message.videoMessage, 'video');
                let chunks = [];
                for await (const chunk of buffer) chunks.push(chunk);
                await manaofc.sendMessage(botUserJid, {
                    video: Buffer.concat(chunks),
                    caption: caption,
                    mimetype: 'video/mp4'
                });
            } else if (msgType === 'audioMessage') {
                const buffer = await downloadContentFromMessage(message.message.audioMessage, 'audio');
                let chunks = [];
                for await (const chunk of buffer) chunks.push(chunk);
                await manaofc.sendMessage(botUserJid, {
                    audio: Buffer.concat(chunks),
                    mimetype: 'audio/mp4',
                    ptt: message.message.audioMessage.ptt || false
                });
            } else if (msgType === 'extendedTextMessage' || msgType === 'conversation') {
                const text = msgType === 'conversation' 
                    ? message.message.conversation 
                    : message.message.extendedTextMessage.text;
                await manaofc.sendMessage(botUserJid, {
                    text: caption + "\n\n📝 *Text:*\n```" + text + "```"
                });
            }
        } catch (error) {
            console.error('Auto status saver error:', error);
        }
    });
}


// ========== DATABASE HELPERS =============

const basePath = path.join(__dirname, "buttondata");
const settingsPath = path.join(basePath, "settings");
const nonBtnPath = path.join(basePath, "Non-Btn");
const settingsFile = path.join(settingsPath, "settings.json");
const nonBtnFile = path.join(nonBtnPath, "data.json");

// Create folders
if (!fs.existsSync(basePath)) {
  fs.mkdirSync(basePath, { recursive: true });
}

if (!fs.existsSync(settingsPath)) {
  fs.mkdirSync(settingsPath, { recursive: true });
}

if (!fs.existsSync(nonBtnPath)) {
  fs.mkdirSync(nonBtnPath, { recursive: true });
}

// ================= DEFAULT SETTINGS =================

const defaultSettings = {
    AUTO_VIEW_STATUS: 'false',
    AUTO_LIKE_STATUS: 'false',
    PRESENCE: 'composing',
    AUTO_LIKE_EMOJI: ['💥', '👍', '😍', '💗', '🎈', '🎉', '🥳', '😎', '🚀', '🔥'],
    AUTO_STATUS_SAVER: 'false',
    PREFIX: '.',
    MAX_RETRIES: 3,
    IMAGE_PATH: 'https://files.catbox.moe/i33owf.png',
    OWNER_NUMBER: '+94759934522',
    BOT_MODE: 'public',
    ANTIDELETE: 'true',
    ANTICALL: 'false',
    BOT_NAME: 'MANISHA-MD',
    FOOTER: '> _*Powered By Manaofc*_',
    ANTICALL_MSG: '📵 Calls are not allowed! Please send a message instead.',
    NON_BUTTON: false
};

// ================= JSON FUNCTIONS =================

function createJSON(file, data) {
  try {
    if (!fs.existsSync(file)) {
      fs.writeFileSync(
        file,
        JSON.stringify(data, null, 2),
        "utf8"
      );
    }
  } catch (error) {
    console.error("JSON create error:", error);
  }
}

function readJSONFile(file, defaultData) {
  try {
    createJSON(file, defaultData);

    const data = fs.readFileSync(file, "utf8");

    if (!data.trim()) {
      return defaultData;
    }

    return JSON.parse(data);
  } catch (error) {
    console.error("JSON read error:", error);
    return defaultData;
  }
}

function writeJSONFile(file, data) {
  try {
    fs.writeFileSync(
      file,
      JSON.stringify(data, null, 2),
      "utf8"
    );

    return true;
  } catch (error) {
    console.error("JSON write error:", error);
    return false;
  }
}

// Create database files
createJSON(settingsFile, defaultSettings);
createJSON(nonBtnFile, []);

// ================= CMD STORE FUNCTIONS =================

async function updateCMDStore(MsgID, CmdID) {
  try {
    const olds = readJSONFile(nonBtnFile, []);

    olds.push({
      [MsgID]: CmdID
    });

    return writeJSONFile(nonBtnFile, olds);
  } catch (error) {
    console.error("updateCMDStore error:", error);
    return false;
  }
}

async function isbtnID(MsgID) {
  try {
    const olds = readJSONFile(nonBtnFile, []);

    return olds.some(
      (item) =>
        Object.prototype.hasOwnProperty.call(item, MsgID)
    );
  } catch (error) {
    console.error("isbtnID error:", error);
    return false;
  }
}

async function getCMDStore(MsgID) {
  try {
    const olds = readJSONFile(nonBtnFile, []);

    for (const item of olds) {
      if (
        Object.prototype.hasOwnProperty.call(item, MsgID)
      ) {
        return item[MsgID];
      }
    }

    return null;
  } catch (error) {
    console.error("getCMDStore error:", error);
    return null;
  }
}

function getCmdForCmdId(CMD_ID_MAP, cmdId) {
  const result = CMD_ID_MAP.find(
    (entry) => entry.cmdId === cmdId
  );

  return result ? result.cmd : null;
}

// ================= DATABASE ECT =================

async function connectdb() {
  try {
    createJSON(settingsFile, defaultSettings);
    createJSON(nonBtnFile, []);

    console.log("Local database connected 💜");
    return true;
  } catch (error) {
    console.error("Database ection error:", error);
    return false;
  }
}

// ================= UPDATE SETTING =================

async function input(setting, data) {
  try {
    const settings = readJSONFile(
      settingsFile,
      defaultSettings
    );

    if (!Object.prototype.hasOwnProperty.call(settings, setting)) {
      console.warn(`Setting "${setting}" is not recognized.`);
      return false;
    }

    settings[setting] = data;

    // Update runtime config
    config[setting] = data;

    // Save locally
    return writeJSONFile(settingsFile, settings);

  } catch (error) {
    console.error("input error:", error);
    return false;
  }
}

// ================= GET SETTING =================

async function get(setting) {
  try {
    const settings = readJSONFile(
      settingsFile,
      defaultSettings
    );

    if (!Object.prototype.hasOwnProperty.call(settings, setting)) {
      console.warn(`Setting "${setting}" is not recognized.`);
      return null;
    }

    return settings[setting];

  } catch (error) {
    console.error("get error:", error);
    return null;
  }
}

// ================= UPDATE CONFIG =================

// ================= UPDATE CONFIG =================

async function updateDB() {
  try {
    const settings = readJSONFile(
      settingsFile,
      defaultSettings
    );

    // Update config from local database
    config.AUTO_VIEW_STATUS = settings.AUTO_VIEW_STATUS;
    config.AUTO_LIKE_STATUS = settings.AUTO_LIKE_STATUS;
    config.AUTO_LIKE_EMOJI = settings.AUTO_LIKE_EMOJI;
    config.AUTO_STATUS_SAVER = settings.AUTO_STATUS_SAVER;
    config.MAX_RETRIES = Number(settings.MAX_RETRIES);
    config.IMAGE_PATH = settings.IMAGE_PATH;
    config.OWNER_NUMBER = settings.OWNER_NUMBER;
    config.BOT_MODE = settings.BOT_MODE;
    config.BOT_NAME = settings.BOT_NAME;
    config.FOOTER = settings.FOOTER;
    config.ANTICALL_MSG = settings.ANTICALL_MSG;
    config.NON_BUTTON = settings.NON_BUTTON;
    config.ANTIDELETE = settings.ANTIDELETE;
    config.ANTICALL = settings.ANTICALL;

    console.log("Local database updated ✅");

    return true;

  } catch (error) {
    console.error("updb error:", error);
    return false;
  }
}


// ================= RESET DATABASE =================

async function updfb() {
  try {
    writeJSONFile(
      settingsFile,
      defaultSettings
    );

    // Update runtime config
    Object.keys(defaultSettings).forEach((key) => {
      config[key] = defaultSettings[key];
    });

    config.MAX_SIZE = Number(defaultSettings.MAX_SIZE);

    console.log("Local database reset ✅");

    return true;

  } catch (error) {
    console.error("updfb error:", error);
    return false;
  }
}

// ================= RESET BUTTON DATABASE =================

async function upresbtn() {
  try {
    writeJSONFile(nonBtnFile, []);

    console.log("Button database cleared ✅");

    return true;

  } catch (error) {
    console.error("upresbtn error:", error);
    return false;
  }
}


// ========== COMMAND REGISTRY ==========
const commands = [];

function cmd(info, func) {
  var data = info;
  data.function = func;
  if (!data.dontAddCommandList) data.dontAddCommandList = false;
  if (!info.desc) info.desc = '';
  if (!data.fromMe) data.fromMe = false;
  if (!info.category) data.category = 'misc';
  if (!info.filename) data.filename = "Not Provided";
  commands.push(data);
  return data;
}

// ========== COMMANDS ==========
// ==================== GAMES MENU ====================
cmd({
    pattern: "games",
    react: "🎮",
    desc: "AIRA ARCADE ZONE - Mini Games Menu",
    category: "games",
    use: ".games",
    filename: __filename
},
async (manaofc, mek, m, { from, reply }) => {
    try {
        const menu = `
╭─── *🎮 AIRA ARCADE ZONE 🎮* ───╮
│
│  *🕹️ Exclusive WhatsApp Mini Games Hub*
│
├─ *🎯 Action Games*
│  • !doom  → Doom 3D (FPS Raycaster)
│  • !space → Galaxy Wars (Space Shooter)
│  • !dino  → Dino Runner (T-Rex Run)
│
├─ *🎰 Casino & Luck*
│  • !slots → Fruit Slots (5-Reel Casino)
│  • !wheel → Lucky Wheel (Spin & Win)
│
├─ *🧩 Classic Arcade*
│  • !ttt   → Tic-Tac-Toe (Neon AI vs Player)
│  • !flappy→ Flappy Aira (Retro Flying)
│  • !snake → Cyber Snake (Classic D-Pad)
│
├─ *🎬 Entertainment*
│  • !music → Music Jukebox (Polyphonic Synth)
│  • !cinema→ Cyber Cinema (Canvas Film)
│  • !sound → Sound Studio (Audio Synth)
│
╰─── *Type any command to play!* ───╯
        `;

        await manaofc.sendMessage(from, {
            image: { url: "https://i.imgur.com/arcade_banner.png" },
            caption: menu,
            contextInfo: {
                externalAdReply: {
                    title: "🎮 AIRA ARCADE ZONE",
                    body: "Exclusive WhatsApp Mini Games Hub",
                    thumbnailUrl: "https://i.imgur.com/game_icon.png",
                    sourceUrl: "https://github.com/",
                    mediaType: 1,
                    renderLargerThumbnail: true
                }
            }
        }, { quoted: mek });

    } catch (e) {
        console.error(e);
        reply("❌ *Failed to load games menu!*");
    }
});

// ==================== TIC TAC TOE ====================
cmd({
    pattern: "ttt",
    react: "❌",
    desc: "Neon Tic-Tac-Toe vs AI",
    category: "games",
    use: ".ttt",
    filename: __filename
},
async (manaofc, mek, m, { from, reply }) => {
    try {
        const htmlContent = `<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>NEON TIC-TAC-TOE</title>
<style>
* { margin: 0; padding: 0; box-sizing: border-box; }
body { 
    background: #0a0a1a; 
    display: flex; 
    justify-content: center; 
    align-items: center; 
    min-height: 100vh; 
    font-family: 'Segoe UI', sans-serif;
}
.container { 
    background: #1a1a3e; 
    border: 2px solid #7b2cbf; 
    border-radius: 20px; 
    padding: 20px; 
    box-shadow: 0 0 30px rgba(123,44,191,0.5);
    max-width: 350px; 
    width: 90%;
}
h1 { 
    text-align: center; 
    color: #c77dff; 
    font-size: 1.5rem; 
    margin-bottom: 10px; 
    text-shadow: 0 0 10px #c77dff;
}
.scoreboard { 
    display: flex; 
    justify-content: space-around; 
    margin-bottom: 15px; 
}
.score { 
    background: #16213e; 
    padding: 8px 15px; 
    border-radius: 10px; 
    text-align: center; 
    color: #fff; 
    font-size: 0.8rem;
}
.score span { 
    display: block; 
    font-size: 1.2rem; 
    font-weight: bold; 
}
.board { 
    display: grid; 
    grid-template-columns: repeat(3, 1fr); 
    gap: 8px; 
    margin-bottom: 15px; 
}
.cell { 
    aspect-ratio: 1; 
    background: #0f3460; 
    border: 2px solid #533483; 
    border-radius: 12px; 
    display: flex; 
    justify-content: center; 
    align-items: center; 
    font-size: 2rem; 
    font-weight: bold; 
    cursor: pointer; 
    transition: all 0.3s;
}
.cell:hover { 
    background: #1a4a7a; 
    transform: scale(1.05);
}
.cell.x { 
    color: #00d9ff; 
    text-shadow: 0 0 15px #00d9ff; 
    border-color: #00d9ff;
}
.cell.o { 
    color: #ff006e; 
    text-shadow: 0 0 15px #ff006e; 
    border-color: #ff006e;
}
.status { 
    text-align: center; 
    color: #fff; 
    margin-bottom: 15px; 
    font-size: 1rem;
}
.buttons { 
    display: flex; 
    gap: 10px; 
}
button { 
    flex: 1; 
    padding: 12px; 
    border: none; 
    border-radius: 10px; 
    font-weight: bold; 
    cursor: pointer; 
    font-size: 0.9rem; 
    transition: 0.3s;
}
.vs-ai { 
    background: #16213e; 
    color: #fff; 
    border: 1px solid #533483;
}
.restart { 
    background: #7b2cbf; 
    color: #fff;
}
button:hover { 
    transform: translateY(-2px); 
    box-shadow: 0 5px 15px rgba(123,44,191,0.4);
}
</style>
</head>
<body>
<div class="container">
    <h1>NEON TIC-TAC-TOE</h1>
    <div class="scoreboard">
        <div class="score">PLAYER (X)<span id="scoreX">0</span></div>
        <div class="score">TIES<span id="scoreTie">0</span></div>
        <div class="score">AIRA (O)<span id="scoreO">0</span></div>
    </div>
    <div class="status" id="status">Tap any square to start!</div>
    <div class="board" id="board">
        <div class="cell" data-index="0"></div>
        <div class="cell" data-index="1"></div>
        <div class="cell" data-index="2"></div>
        <div class="cell" data-index="3"></div>
        <div class="cell" data-index="4"></div>
        <div class="cell" data-index="5"></div>
        <div class="cell" data-index="6"></div>
        <div class="cell" data-index="7"></div>
        <div class="cell" data-index="8"></div>
    </div>
    <div class="buttons">
        <button class="vs-ai" onclick="resetGame()">VS AIRA 🤖</button>
        <button class="restart" onclick="resetGame()">RESTART 🔄</button>
    </div>
</div>
<script>
let board = ['','','','','','','','',''];
let currentPlayer = 'X';
let gameActive = true;
let scores = { X: 0, O: 0, tie: 0 };

const winCombos = [
    [0,1,2],[3,4,5],[6,7,8],
    [0,3,6],[1,4,7],[2,5,8],
    [0,4,8],[2,4,6]
];

document.querySelectorAll('.cell').forEach(cell => {
    cell.addEventListener('click', () => {
        const idx = cell.dataset.index;
        if(board[idx] === '' && gameActive && currentPlayer === 'X') {
            makeMove(idx, 'X');
            if(gameActive) setTimeout(aiMove, 500);
        }
    });
});

function makeMove(idx, player) {
    board[idx] = player;
    const cell = document.querySelector('[data-index="'+idx+'"]');
    cell.textContent = player;
    cell.classList.add(player.toLowerCase());
    checkWinner();
    if(gameActive) {
        currentPlayer = player === 'X' ? 'O' : 'X';
        document.getElementById('status').textContent = currentPlayer === 'X' ? 'Your turn' : "Aira's turn... 🤖";
    }
}

function aiMove() {
    let bestScore = -Infinity;
    let move;
    for(let i=0; i<9; i++) {
        if(board[i] === '') {
            board[i] = 'O';
            let score = minimax(board, 0, false);
            board[i] = '';
            if(score > bestScore) { bestScore = score; move = i; }
        }
    }
    makeMove(move, 'O');
}

function minimax(board, depth, isMaximizing) {
    let result = checkWin();
    if(result !== null) return result === 'O' ? 10-depth : result === 'X' ? depth-10 : 0;

    if(isMaximizing) {
        let bestScore = -Infinity;
        for(let i=0; i<9; i++) {
            if(board[i] === '') {
                board[i] = 'O';
                let score = minimax(board, depth+1, false);
                board[i] = '';
                bestScore = Math.max(score, bestScore);
            }
        }
        return bestScore;
    } else {
        let bestScore = Infinity;
        for(let i=0; i<9; i++) {
            if(board[i] === '') {
                board[i] = 'X';
                let score = minimax(board, depth+1, true);
                board[i] = '';
                bestScore = Math.min(score, bestScore);
            }
        }
        return bestScore;
    }
}

function checkWinner() {
    let winner = checkWin();
    if(winner !== null) {
        gameActive = false;
        if(winner === 'tie') {
            scores.tie++;
            document.getElementById('status').textContent = "🤝 It's a tie!";
        } else {
            scores[winner]++;
            document.getElementById('status').textContent = winner === 'X' ? "🎉 You Win!" : "🤖 Aira Wins!";
        }
        updateScores();
    }
}

function checkWin() {
    for(let combo of winCombos) {
        const [a,b,c] = combo;
        if(board[a] && board[a] === board[b] && board[a] === board[c]) return board[a];
    }
    if(!board.includes('')) return 'tie';
    return null;
}

function updateScores() {
    document.getElementById('scoreX').textContent = scores.X;
    document.getElementById('scoreO').textContent = scores.O;
    document.getElementById('scoreTie').textContent = scores.tie;
}

function resetGame() {
    board = ['','','','','','','','',''];
    currentPlayer = 'X';
    gameActive = true;
    document.querySelectorAll('.cell').forEach(c => { c.textContent = ''; c.className = 'cell'; });
    document.getElementById('status').textContent = 'Tap any square to start!';
}
</script>
</body>
</html>`;

        const filePath = path.join(__dirname, 'ttt_game.html');
        fs.writeFileSync(filePath, htmlContent);

        await manaofc.sendMessage(from, {
            document: fs.readFileSync(filePath),
            mimetype: 'text/html',
            fileName: 'NEON_TIC_TAC_TOE.html',
            caption: '🎮 *NEON TIC-TAC-TOE*\n❌ You vs 🤖 Aira (AI)\n\n_Tap the file to play!_'
        }, { quoted: mek });

        fs.unlinkSync(filePath);

    } catch (e) {
        console.error(e);
        reply("❌ *Failed to launch Tic-Tac-Toe!*");
    }
});

// ==================== GALAXY SHOOTER ====================
cmd({
    pattern: "space",
    react: "🚀",
    desc: "Galaxy Wars - Space Alien Shooter",
    category: "games",
    use: ".space",
    filename: __filename
},
async (manaofc, mek, m, { from, reply }) => {
    try {
        const htmlContent = `<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0, user-scalable=no">
<title>GALAXY SHOOTER 🚀</title>
<style>
* { margin: 0; padding: 0; box-sizing: border-box; overflow: hidden; }
body { background: #050510; display: flex; justify-content: center; align-items: center; height: 100vh; font-family: 'Segoe UI', sans-serif; }
#gameContainer { position: relative; width: 100%; max-width: 400px; height: 100vh; max-height: 700px; background: #0a0a1a; border: 2px solid #9d4edd; border-radius: 15px; overflow: hidden; }
#canvas { display: block; width: 100%; height: 100%; }
#ui { position: absolute; top: 0; left: 0; right: 0; padding: 15px; display: flex; justify-content: space-between; color: #fff; font-weight: bold; font-size: 1rem; z-index: 10; }
#startScreen, #gameOverScreen { position: absolute; inset: 0; background: rgba(5,5,16,0.95); display: flex; flex-direction: column; justify-content: center; align-items: center; z-index: 20; }
#startScreen h1, #gameOverScreen h1 { color: #c77dff; font-size: 2rem; margin-bottom: 10px; text-shadow: 0 0 20px #c77dff; }
#startScreen p, #gameOverScreen p { color: #aaa; margin-bottom: 20px; }
.btn { padding: 15px 40px; background: #7b2cbf; color: #fff; border: none; border-radius: 25px; font-size: 1.1rem; font-weight: bold; cursor: pointer; box-shadow: 0 0 20px rgba(123,44,191,0.5); transition: 0.3s; }
.btn:hover { transform: scale(1.05); box-shadow: 0 0 30px rgba(123,44,191,0.8); }
.hidden { display: none !important; }
</style>
</head>
<body>
<div id="gameContainer">
    <div id="ui">
        <div>SCORE: <span id="score">0</span></div>
        <div>LIVES: <span id="lives">❤️❤️❤️</span></div>
    </div>
    <canvas id="canvas"></canvas>
    <div id="startScreen">
        <h1>GALAXY SHOOTER 🚀</h1>
        <p>Drag ship to Move & Shoot Aliens!</p>
        <button class="btn" onclick="startGame()">LAUNCH FIGHTER 🛸</button>
    </div>
    <div id="gameOverScreen" class="hidden">
        <h1>GAME OVER</h1>
        <p>Final Score: <span id="finalScore">0</span></p>
        <button class="btn" onclick="resetGame()">TRY AGAIN 🔄</button>
    </div>
</div>
<script>
const canvas = document.getElementById('canvas');
const ctx = canvas.getContext('2d');
let W, H, animationId, score, lives, gameRunning;
let player, bullets, enemies, particles, stars;

function resize() {
    const container = document.getElementById('gameContainer');
    W = canvas.width = container.clientWidth;
    H = canvas.height = container.clientHeight;
}
window.addEventListener('resize', resize);
resize();

class Player {
    constructor() { this.w = 40; this.h = 40; this.x = W/2 - this.w/2; this.y = H - 80; this.speed = 5; }
    draw() {
        ctx.fillStyle = '#00d9ff';
        ctx.shadowBlur = 15; ctx.shadowColor = '#00d9ff';
        ctx.beginPath();
        ctx.moveTo(this.x + this.w/2, this.y);
        ctx.lineTo(this.x + this.w, this.y + this.h);
        ctx.lineTo(this.x + this.w/2, this.y + this.h - 10);
        ctx.lineTo(this.x, this.y + this.h);
        ctx.closePath();
        ctx.fill();
        ctx.shadowBlur = 0;
    }
    update() {
        if(touchX !== null) {
            this.x += (touchX - this.x - this.w/2) * 0.15;
        }
        this.x = Math.max(0, Math.min(W - this.w, this.x));
    }
}

class Bullet {
    constructor(x, y) { this.x = x; this.y = y; this.w = 4; this.h = 15; this.speed = 8; }
    draw() {
        ctx.fillStyle = '#00d9ff';
        ctx.shadowBlur = 10; ctx.shadowColor = '#00d9ff';
        ctx.fillRect(this.x - this.w/2, this.y, this.w, this.h);
        ctx.shadowBlur = 0;
    }
    update() { this.y -= this.speed; }
}

class Enemy {
    constructor(x, y, type) {
        this.x = x; this.y = y; this.w = 35; this.h = 35; this.type = type;
        this.speedX = (Math.random() - 0.5) * 2;
        this.speedY = 0.5 + Math.random() * 1;
        this.colors = ['#ff006e', '#fb5607', '#ffbe0b', '#8338ec', '#3a86ff'];
    }
    draw() {
        ctx.fillStyle = this.colors[this.type % this.colors.length];
        ctx.shadowBlur = 10; ctx.shadowColor = ctx.fillStyle;
        ctx.beginPath();
        ctx.arc(this.x + this.w/2, this.y + this.h/2, this.w/2, 0, Math.PI * 2);
        ctx.fill();
        ctx.fillStyle = '#fff';
        ctx.beginPath();
        ctx.arc(this.x + this.w/2 - 6, this.y + this.h/2 - 3, 4, 0, Math.PI * 2);
        ctx.arc(this.x + this.w/2 + 6, this.y + this.h/2 - 3, 4, 0, Math.PI * 2);
        ctx.fill();
        ctx.shadowBlur = 0;
    }
    update() {
        this.x += this.speedX;
        this.y += this.speedY;
        if(this.x <= 0 || this.x >= W - this.w) this.speedX *= -1;
    }
}

class Particle {
    constructor(x, y, color) {
        this.x = x; this.y = y; this.vx = (Math.random() - 0.5) * 6;
        this.vy = (Math.random() - 0.5) * 6; this.life = 1;
        this.color = color;
    }
    draw() {
        ctx.globalAlpha = this.life;
        ctx.fillStyle = this.color;
        ctx.fillRect(this.x, this.y, 3, 3);
        ctx.globalAlpha = 1;
    }
    update() { this.x += this.vx; this.y += this.vy; this.life -= 0.02; }
}

class Star {
    constructor() { this.x = Math.random() * W; this.y = Math.random() * H; this.size = Math.random() * 2; this.speed = Math.random() * 2 + 0.5; }
    draw() { ctx.fillStyle = '#fff'; ctx.globalAlpha = Math.random() * 0.5 + 0.3; ctx.fillRect(this.x, this.y, this.size, this.size); ctx.globalAlpha = 1; }
    update() { this.y += this.speed; if(this.y > H) { this.y = 0; this.x = Math.random() * W; } }
}

let touchX = null;
canvas.addEventListener('touchmove', e => { e.preventDefault(); touchX = e.touches[0].clientX - canvas.getBoundingClientRect().left; }, {passive: false});
canvas.addEventListener('touchstart', e => { e.preventDefault(); touchX = e.touches[0].clientX - canvas.getBoundingClientRect().left; fireBullet(); }, {passive: false});
canvas.addEventListener('mousemove', e => { touchX = e.clientX - canvas.getBoundingClientRect().left; });
canvas.addEventListener('mousedown', () => fireBullet());

function fireBullet() {
    if(!gameRunning) return;
    bullets.push(new Bullet(player.x + player.w/2, player.y));
}

function createExplosion(x, y, color) {
    for(let i=0; i<15; i++) particles.push(new Particle(x, y, color));
}

function spawnEnemies() {
    if(Math.random() < 0.03) {
        const cols = 6;
        const x = Math.random() * (W - 40);
        enemies.push(new Enemy(x, -40, Math.floor(Math.random() * 5)));
    }
}

function checkCollisions() {
    for(let i = bullets.length - 1; i >= 0; i--) {
        for(let j = enemies.length - 1; j >= 0; j--) {
            const b = bullets[i], e = enemies[j];
            if(b && e && b.x > e.x && b.x < e.x + e.w && b.y > e.y && b.y < e.y + e.h) {
                createExplosion(e.x + e.w/2, e.y + e.h/2, e.colors[e.type % e.colors.length]);
                score += 20;
                bullets.splice(i, 1);
                enemies.splice(j, 1);
                break;
            }
        }
    }
    for(let j = enemies.length - 1; j >= 0; j--) {
        const e = enemies[j];
        if(e.y > H) { enemies.splice(j, 1); continue; }
        if(e.x < player.x + player.w && e.x + e.w > player.x && e.y < player.y + player.h && e.y + e.h > player.y) {
            createExplosion(player.x + player.w/2, player.y + player.h/2, '#00d9ff');
            lives--; enemies.splice(j, 1);
            if(lives <= 0) endGame();
        }
    }
}

function updateUI() {
    document.getElementById('score').textContent = score;
    document.getElementById('lives').textContent = '❤️'.repeat(Math.max(0, lives));
}

function gameLoop() {
    if(!gameRunning) return;
    ctx.fillStyle = '#050510'; ctx.fillRect(0, 0, W, H);
    stars.forEach(s => { s.update(); s.draw(); });
    player.update(); player.draw();
    bullets.forEach((b, i) => { b.update(); b.draw(); if(b.y < 0) bullets.splice(i, 1); });
    enemies.forEach(e => { e.update(); e.draw(); });
    particles.forEach((p, i) => { p.update(); p.draw(); if(p.life <= 0) particles.splice(i, 1); });
    spawnEnemies(); checkCollisions(); updateUI();
    animationId = requestAnimationFrame(gameLoop);
}

function startGame() {
    document.getElementById('startScreen').classList.add('hidden');
    player = new Player(); bullets = []; enemies = []; particles = []; stars = [];
    for(let i=0; i<50; i++) stars.push(new Star());
    score = 0; lives = 3; gameRunning = true;
    gameLoop();
}

function endGame() {
    gameRunning = false;
    cancelAnimationFrame(animationId);
    document.getElementById('finalScore').textContent = score;
    document.getElementById('gameOverScreen').classList.remove('hidden');
}

function resetGame() {
    document.getElementById('gameOverScreen').classList.add('hidden');
    startGame();
}
</script>
</body>
</html>`;

        const filePath = path.join(__dirname, 'galaxy_shooter.html');
        fs.writeFileSync(filePath, htmlContent);

        await manaofc.sendMessage(from, {
            document: fs.readFileSync(filePath),
            mimetype: 'text/html',
            fileName: 'GALAXY_SHOOTER.html',
            caption: '🚀 *GALAXY SHOOTER*\n👾 Destroy alien invaders!\n\n_Tap the file to play!_'
        }, { quoted: mek });

        fs.unlinkSync(filePath);

    } catch (e) {
        console.error(e);
        reply("❌ *Failed to launch Galaxy Shooter!*");
    }
});

// ==================== DINO RUNNER ====================
cmd({
    pattern: "dino",
    react: "🦖",
    desc: "Dino Runner - Chrome T-Rex Run",
    category: "games",
    use: ".dino",
    filename: __filename
},
async (manaofc, mek, m, { from, reply }) => {
    try {
        const htmlContent = `<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0, user-scalable=no">
<title>NIXEL DINO - Dino Runner 🦖</title>
<style>
* { margin: 0; padding: 0; box-sizing: border-box; overflow: hidden; }
body { background: #1a1a1a; display: flex; justify-content: center; align-items: center; height: 100vh; font-family: 'Courier New', monospace; }
#gameContainer { position: relative; width: 100%; max-width: 400px; height: 100vh; max-height: 250px; background: #2d5a3d; border: 3px solid #1a3c2a; border-radius: 10px; overflow: hidden; }
#canvas { display: block; width: 100%; height: 100%; }
#ui { position: absolute; top: 10px; right: 15px; color: #fff; font-size: 1.2rem; font-weight: bold; z-index: 10; text-shadow: 2px 2px 0 #000; }
#best { position: absolute; top: 10px; left: 15px; color: #fff; font-size: 0.9rem; z-index: 10; text-shadow: 1px 1px 0 #000; }
#gameOver { position: absolute; inset: 0; background: rgba(0,0,0,0.7); display: none; flex-direction: column; justify-content: center; align-items: center; z-index: 20; }
#gameOver h1 { color: #fff; font-size: 1.5rem; margin-bottom: 10px; }
#gameOver p { color: #aaa; font-size: 0.9rem; }
</style>
</head>
<body>
<div id="gameContainer">
    <div id="best">BEST <span id="bestScore">00000</span></div>
    <div id="ui"><span id="score">00000</span></div>
    <canvas id="canvas"></canvas>
    <div id="gameOver">
        <h1>GAME OVER</h1>
        <p>Tap Screen to Restart</p>
    </div>
</div>
<script>
const canvas = document.getElementById('canvas');
const ctx = canvas.getContext('2d');
let W, H, gameLoop, score, bestScore = localStorage.getItem('dinoBest') || 0, speed, gameOver;
let dino, obstacles, clouds, groundY;

function resize() {
    const container = document.getElementById('gameContainer');
    W = canvas.width = container.clientWidth;
    H = canvas.height = container.clientHeight;
    groundY = H - 30;
}
window.addEventListener('resize', resize);
resize();
document.getElementById('bestScore').textContent = String(bestScore).padStart(5, '0');

class Dino {
    constructor() { this.w = 30; this.h = 40; this.x = 50; this.y = groundY - this.h; this.vy = 0; this.gravity = 0.8; this.jumpPower = -14; this.grounded = true; this.legFrame = 0; }
    jump() { if(this.grounded) { this.vy = this.jumpPower; this.grounded = false; } }
    update() {
        this.vy += this.gravity; this.y += this.vy;
        if(this.y >= groundY - this.h) { this.y = groundY - this.h; this.vy = 0; this.grounded = true; }
        if(!this.grounded) this.legFrame = 0; else this.legFrame += 0.2;
    }
    draw() {
        ctx.fillStyle = '#fff';
        // Body
        ctx.fillRect(this.x + 8, this.y, 14, 20);
        // Head
        ctx.fillRect(this.x + 14, this.y - 10, 16, 14);
        // Eye
        ctx.fillStyle = '#2d5a3d'; ctx.fillRect(this.x + 24, this.y - 6, 3, 3); ctx.fillStyle = '#fff';
        // Legs
        if(Math.floor(this.legFrame) % 2 === 0) {
            ctx.fillRect(this.x + 8, this.y + 20, 6, 12);
            ctx.fillRect(this.x + 16, this.y + 20, 6, 10);
        } else {
            ctx.fillRect(this.x + 8, this.y + 20, 6, 10);
            ctx.fillRect(this.x + 16, this.y + 20, 6, 12);
        }
        // Tail
        ctx.fillRect(this.x, this.y + 5, 10, 6);
    }
}

class Obstacle {
    constructor() {
        this.w = 20 + Math.random() * 15;
        this.h = 30 + Math.random() * 20;
        this.x = W + this.w;
        this.y = groundY - this.h;
        this.type = Math.random() > 0.5 ? 'cactus' : 'rock';
    }
    update() { this.x -= speed; }
    draw() {
        if(this.type === 'cactus') {
            ctx.fillStyle = '#e76f51';
            ctx.fillRect(this.x + this.w/3, this.y, this.w/3, this.h);
            ctx.fillRect(this.x, this.y + this.h/3, this.w/3, this.h/4);
            ctx.fillRect(this.x + this.w*2/3, this.y + this.h/4, this.w/3, this.h/4);
        } else {
            ctx.fillStyle = '#6c757d';
            ctx.fillRect(this.x, this.y + 10, this.w, this.h - 10);
        }
    }
}

class Cloud {
    constructor() { this.x = W + 50; this.y = Math.random() * (H/2); this.w = 40 + Math.random() * 30; this.speed = 0.5 + Math.random() * 0.5; }
    update() { this.x -= this.speed; }
    draw() { ctx.fillStyle = 'rgba(255,255,255,0.3)'; ctx.fillRect(this.x, this.y, this.w, 12); ctx.fillRect(this.x + 10, this.y - 8, this.w - 20, 10); }
}

function drawGround() {
    ctx.strokeStyle = '#1a3c2a'; ctx.lineWidth = 2;
    ctx.beginPath(); ctx.moveTo(0, groundY); ctx.lineTo(W, groundY); ctx.stroke();
    for(let i=0; i<W; i+=20) { const offset = (i - (score * speed * 0.1)) % 20; ctx.fillStyle = '#1a3c2a'; ctx.fillRect(i - offset, groundY + 5, 4, 4); }
}

function spawnObstacle() {
    if(Math.random() < 0.015 && (obstacles.length === 0 || W - obstacles[obstacles.length-1].x > 200)) {
        obstacles.push(new Obstacle());
    }
}

function checkCollisions() {
    for(let obs of obstacles) {
        if(dino.x + dino.w - 5 > obs.x + 5 && dino.x + 5 < obs.x + obs.w - 5 && dino.y + dino.h - 5 > obs.y + 5) {
            endGame(); return;
        }
    }
}

function update() {
    if(gameOver) return;
    ctx.fillStyle = '#2d5a3d'; ctx.fillRect(0, 0, W, H);
    clouds.forEach((c, i) => { c.update(); c.draw(); if(c.x < -c.w) clouds.splice(i, 1); });
    if(Math.random() < 0.01) clouds.push(new Cloud());
    drawGround();
    dino.update(); dino.draw();
    obstacles.forEach((o, i) => { o.update(); o.draw(); if(o.x < -o.w) obstacles.splice(i, 1); });
    spawnObstacle(); checkCollisions();
    score++; speed = 5 + Math.floor(score / 500);
    document.getElementById('score').textContent = String(score).padStart(5, '0');
    gameLoop = requestAnimationFrame(update);
}

function startGame() {
    dino = new Dino(); obstacles = []; clouds = []; score = 0; speed = 5; gameOver = false;
    document.getElementById('gameOver').style.display = 'none';
    for(let i=0; i<5; i++) { let c = new Cloud(); c.x = Math.random() * W; clouds.push(c); }
    update();
}

function endGame() {
    gameOver = true; cancelAnimationFrame(gameLoop);
    if(score > bestScore) { bestScore = score; localStorage.setItem('dinoBest', bestScore); document.getElementById('bestScore').textContent = String(bestScore).padStart(5, '0'); }
    document.getElementById('gameOver').style.display = 'flex';
}

function reset() { if(gameOver) startGame(); else dino.jump(); }

document.addEventListener('keydown', e => { if(e.code === 'Space' || e.code === 'ArrowUp') { e.preventDefault(); reset(); } });
canvas.addEventListener('touchstart', e => { e.preventDefault(); reset(); }, {passive: false});
canvas.addEventListener('mousedown', reset);

startGame();
</script>
</body>
</html>`;

        const filePath = path.join(__dirname, 'dino_runner.html');
        fs.writeFileSync(filePath, htmlContent);

        await manaofc.sendMessage(from, {
            document: fs.readFileSync(filePath),
            mimetype: 'text/html',
            fileName: 'NIXEL_DINO_RUNNER.html',
            caption: '🦖 *NIXEL DINO RUNNER*\n🏃 Jump over obstacles!\n\n_Tap the file to play!_'
        }, { quoted: mek });

        fs.unlinkSync(filePath);

    } catch (e) {
        console.error(e);
        reply("❌ *Failed to launch Dino Runner!*");
    }
});

// ==================== EXTRA GAME PLACEHOLDERS ====================
const gameCommands = [
    { pattern: "flappy", react: "🐥", name: "Flappy Aira", desc: "Retro Arcade Flying", color: "#FFD700" },
    { pattern: "snake", react: "🐍", name: "Cyber Snake", desc: "Classic D-Pad Snake", color: "#32CD32" },
    { pattern: "slots", react: "🎰", name: "Fruit Slots", desc: "5-Reel Casino Slots", color: "#FF6347" },
    { pattern: "wheel", react: "🎡", name: "Lucky Wheel", desc: "Spin & Win Jackpots", color: "#FF69B4" },
    { pattern: "music", react: "🎵", name: "Music Jukebox", desc: "Polyphonic Synth & Vis", color: "#9370DB" },
    { pattern: "cinema", react: "🎬", name: "Cyber Cinema", desc: "Animated Canvas Film", color: "#20B2AA" },
    { pattern: "sound", react: "🔊", name: "Sound Studio", desc: "Audio Synth & Melody", color: "#87CEEB" },
    { pattern: "doom", react: "💥", name: "Doom 3D", desc: "3D FPS Raycaster", color: "#DC143C" }
];

gameCommands.forEach(game => {
    cmd({
        pattern: game.pattern,
        react: game.react,
        desc: game.name + " - " + game.desc,
        category: "games",
        use: "." + game.pattern,
        filename: __filename
    },
    async (manaofc, mek, m, { from, reply }) => {
        try {
            const htmlContent = `<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>${game.name} ${game.react}</title>
<style>
* { margin: 0; padding: 0; box-sizing: border-box; }
body { background: #0a0a1a; display: flex; justify-content: center; align-items: center; min-height: 100vh; font-family: 'Segoe UI', sans-serif; }
.container { text-align: center; padding: 40px; background: #1a1a3e; border: 2px solid ${game.color}; border-radius: 20px; box-shadow: 0 0 30px ${game.color}40; }
h1 { color: ${game.color}; font-size: 2rem; margin-bottom: 10px; text-shadow: 0 0 20px ${game.color}; }
p { color: #aaa; margin-bottom: 20px; }
.coming-soon { color: #fff; font-size: 1.2rem; padding: 20px; border: 2px dashed ${game.color}; border-radius: 10px; }
</style>
</head>
<body>
<div class="container">
    <h1>${game.name} ${game.react}</h1>
    <p>${game.desc}</p>
    <div class="coming-soon">🚧 Full game coming soon! 🚧<br><br>Try:<br>!ttt - Tic-Tac-Toe<br>!space - Galaxy Shooter<br>!dino - Dino Runner</div>
</div>
</body>
</html>`;

            const filePath = path.join(__dirname, game.pattern + '_game.html');
            fs.writeFileSync(filePath, htmlContent);

            await manaofc.sendMessage(from, {
                document: fs.readFileSync(filePath),
                mimetype: 'text/html',
                fileName: game.name.replace(/\s/g, '_') + '.html',
                caption: `${game.react} *${game.name}*\n${game.desc}\n\n_Tap the file to preview!_`
            }, { quoted: mek });

            fs.unlinkSync(filePath);

        } catch (e) {
            console.error(e);
            reply(`❌ *Failed to launch ${game.name}!*`);
        }
    });
});
//====================================
//====== SETTINGS COMMAND =============
//=====================================
//==============
cmd({
    pattern: "settings",
    react: "⚙️",
    alias: ["setup", "changesettings"],
    desc: "Show bot settings menu",
    category: "settings",
    use: ".settings",
    filename: __filename
},
async (manaofc, mek, m, { from, prefix, reply, isOwner, config }) => {
    try {
        if (!isOwner) return reply("❌ *Only owner can use this!*");

        const botNumber = manaofc.user.id.split(":")[0].split("@")[0];
        // using global config

        const sections = [
            {
                title: "🔤 PREFIX",
                rows: [
                    { title: "🔹 Prefix ( . )", rowId: prefix + "set prefix ." },
                    { title: "🔹 Prefix ( ! )", rowId: prefix + "set prefix !" },
                    { title: "🔹 Prefix ( # )", rowId: prefix + "set prefix #" },
                    { title: "🔹 Prefix ( / )", rowId: prefix + "set prefix /" },
                    { title: "🔹 Prefix ( * )", rowId: prefix + "set prefix *" },
                    { title: "🔹 Prefix ( $ )", rowId: prefix + "set prefix $" },
                ],
            },
            {
                title: "🔧 WORK TYPE",
                rows: [
                    { title: "👥 Public", rowId: prefix + "set botmode public" },
                    { title: "👤 Only Me (Private)", rowId: prefix + "set botmode private" },
                ],
            },
            {
                title: "🤖 BOT PRESENCE",
                rows: [
                    { title: "💬 Auto Typing", rowId: prefix + "set presence composing" },
                    { title: "🎙️ Auto Recording", rowId: prefix + "set presence recording" },
                    { title: "🔋 Always Online", rowId: prefix + "set presence available" },
                    { title: "🪫 Always Offline", rowId: prefix + "set presence unavailable" },
                ],
            },
            {
                title: "👁️ AUTO VIEW STATUS",
                rows: [
                    { title: "✅ Turn ON", rowId: prefix + "set autoview on" },
                    { title: "❎ Turn OFF", rowId: prefix + "set autoview off" },
                ],
            },
            {
                title: "❤️ AUTO LIKE STATUS",
                rows: [
                    { title: "✅ Turn ON", rowId: prefix + "set autolike on" },
                    { title: "❎ Turn OFF", rowId: prefix + "set autolike off" },
                ],
            },
            {
                title: "💾 AUTO STATUS SAVER",
                rows: [
                    { title: "✅ Turn ON", rowId: prefix + "set autosave on" },
                    { title: "❎ Turn OFF", rowId: prefix + "set autosave off" },
                ],
            },
            {
                title: "📞 AUTO REJECT CALL",
                rows: [
                    { title: "✅ Turn ON", rowId: prefix + "set anticall on" },
                    { title: "❎ Turn OFF", rowId: prefix + "set anticall off" },
                ],
            },
            {
                title: "🗑️ ANTI DELETE",
                rows: [
                    { title: "✅ Turn ON", rowId: prefix + "set antidelete on" },
                    { title: "❎ Turn OFF", rowId: prefix + "set antidelete off" },
                ],
            },
            {
                title: "🔘 NON BUTTON MODE",
                rows: [
                    { title: "✅ Turn ON (Text Mode)", rowId: prefix + "set nonbutton on" },
                    { title: "❎ Turn OFF (Button Mode)", rowId: prefix + "set nonbutton off" },
                ],
            },
        ];

        const desc = `⚙️ \`${config.BOT_NAME || 'MANAOFC LITE'} SETTINGS\` ⚙️

> ◈ *Owner:* manaofc
> ◈ *Version:* ${version}
> ◈ *Prefix:* ${config.PREFIX || '.'}
> ◈ *Mode:* ${(config.BOT_MODE || 'public').toUpperCase()}`;

        let listset = {
            text: desc,
            footer: config.FOOTER || config.FOOTER,
            //title: "",
            buttonText: "🖱️ button options cliq",
            sections,
        };
        await manaofc.listMessage(from, listset, mek);

    } catch (e) {
        console.error(e);
        reply(`❌ Error: ${e.message}`);
    }
});

//==============
cmd({
    pattern: "set",
    react: "🔧",
    dontAddCommandList: true,
    filename: __filename
},
async (manaofc, mek, m, { from, q, reply, isOwner, config }) => {
    try {
        if (!isOwner) return reply("❌ *Only owner can use this!*");

        const botNumber = manaofc.user.id.split(":")[0].split("@")[0];
        // config already available

        if (!q) {
            return reply("❌ *Provide a value!*\nExample: `.set prefix !`");
        }

        const args = q.trim().split(/ +/);
        const field = args[0].toLowerCase();
        const value = args.slice(1).join(" ");

        if (!value) {
            return reply("❌ *Provide a value!*\nExample: `.set prefix !`");
        }

        const updates = { };

        switch (field) {
            case 'prefix':
                updates.PREFIX = value;
                break;
            case 'botmode':
            case 'mode':
                if (!['public','private','inbox','group'].includes(value.toLowerCase())) {
                    return reply("❌ *Valid modes:* public, private, inbox, group");
                }
                updates.BOT_MODE = value.toLowerCase();
                break;
            case 'presence':
                if (!['composing','recording','available','unavailable'].includes(value.toLowerCase())) {
                    return reply("❌ *Valid presence:* composing, recording, available, unavailable");
                }
                updates.PRESENCE = value.toLowerCase();
                break;
            case 'autoview':
            case 'auto_view_status':
                updates.AUTO_VIEW_STATUS = value.toLowerCase() === 'on' || value === 'true' ? 'true' : 'false';
                break;
            case 'autolike':
            case 'auto_like_status':
                updates.AUTO_LIKE_STATUS = value.toLowerCase() === 'on' || value === 'true' ? 'true' : 'false';
                break;
            case 'autosave':
            case 'auto_status_saver':
                updates.AUTO_STATUS_SAVER = value.toLowerCase() === 'on' || value === 'true' ? 'true' : 'false';
                break;
            case 'antidelete':
                updates.ANTIDELETE = value.toLowerCase() === 'on' || value === 'true' ? 'true' : 'false';
                break;
            case 'anticall':
                updates.ANTICALL = value.toLowerCase() === 'on' || value === 'true' ? 'true' : 'false';
                break;
            case 'nonbutton':
            case 'non_button':
                updates.NON_BUTTON = value.toLowerCase() === 'on' || value === 'true' ? true : false;
                break;
            default:
                return reply("❌ *Unknown field!*\nTry: `.set prefix !`");
        }

        for (const [key, value] of Object.entries(updates)) {
            await input(key, value);
        }
        reply(`✅ *Setting updated!*\n\n*${field}* → ${value}\n\n_Bot will apply changes immediately._`);

    } catch (e) {
        console.error(e);
        reply(`❌ Error: ${e.message}`);
    }
});

//=========

cmd(
{
    pattern: "getconfig",
    alias: ["config", "botconfig", "currentsettings"],
    desc: "View all current bot settings",
    category: "settings",
    react: "📋",
    use: ".getconfig",
    filename: __filename
},
async (manaofc, mek, m, { from, reply, isOwner }) => {
    try {
        if (!isOwner) {
            return reply("❌ *Only owner can use this command!*");
        }

        const botNumber = manaofc.user.id.split(":")[0].split("@")[0];
        // config already available from outer scope

        let configText = "";

      configText += `🤖 *${config.BOT_NAME || config.BOT_NAME}*\n\n`;
      configText += "📋 *CURRENT BOT CONFIGURATION* 📋\n\n";
      configText += `🔢 *Bot Number:* ${botNumber}\n`;
      configText += `⏰ *Time:* ${getSriLankaTimestamp()}\n\n`;
      configText += "*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n";
      configText += `*╎ 🔧 BOT_MODE:* ${(config.BOT_MODE || "public").toUpperCase()}\n`;
      configText += `*╎ 🎭 PRESENCE:* ${
        config.PRESENCE
        ? config.PRESENCE.toUpperCase()
        : "AVAILABLE"
      }\n`;
      configText += `*╎ 👁️ AUTO_VIEW_STATUS:* ${
        config.AUTO_VIEW_STATUS === "true" ? "✅ ON" : "❌ OFF"
      }\n`;
      configText += `*╎ 🛟 AUTO_LIKE_STATUS:* ${
        config.AUTO_LIKE_STATUS === "true" ? "✅ ON" : "❌ OFF"
      }\n`;
      configText += `*╎ 📱 AUTO_STATUS_SAVER:* ${
        config.AUTO_STATUS_SAVER === "true" ? "✅ ON" : "❌ OFF"
      }\n`;
      configText += `*╎ 📞 ANTICALL:* ${
        config.ANTICALL === "true" ? "✅ ON" : "❌ OFF"
      }\n`;
      configText += `*╎ 🗑️ ANTIDELETE:* ${
        config.ANTIDELETE === "true" ? "✅ ON" : "❌ OFF"
      }\n`;
      configText += `*╎ 🔤 PREFIX:* ${config.PREFIX || "."}\n`;
      configText += `*╎ 🎨 LIKE_EMOJIS:* ${
        Array.isArray(config.AUTO_LIKE_EMOJI)
        ? config.AUTO_LIKE_EMOJI.join(" ")
        : (config.AUTO_LIKE_EMOJI || "❤️")
      }\n`;
      configText += `*╎ 🔘 NON_BUTTON:* ${
        config.NON_BUTTON === true ? "✅ ON (Text Mode)" : "❌ OFF (Button Mode)"
      }\n`;
      configText += "*╰━━━━━━━✧༺♥༻✧━━━━━━━*";
      
        await manaofc.sendMessage(
            from,
            {
                image: {
                    url: config.IMAGE_PATH || config.IMAGE_PATH
                },
                caption: configText
            },
            {
                quoted: mek
            }
        );

    } catch (e) {
        console.error("[GETCONFIG ERROR]:", e);
        reply(`❌ Error: ${e.message}`);
    }
});


//====================================
//========= MAIN COMMAND =============
//====================================

cmd({
  pattern: "menu",
  react: "📃",
  alias: ["panel","list","commands"],
  desc: "Get bot's command list.",
  category: "main",
  use: '.menu',
  filename: __filename
},
async(manaofc, mek, m,{from, prefix, pushname, reply, config}) => {
try{
if(os.hostname().length == 12 ) hostname = 'replit'
else if(os.hostname().length == 36) hostname = 'heroku'
else if(os.hostname().length == 8) hostname = 'koyeb'
else hostname = os.hostname()
let monspace ='```'
const buttons = [
{buttonId: prefix + 'downmenu' , buttonText: {displayText: 'DOWNLOAD MENU'}, type: 1},
{buttonId: prefix + 'ownermenu' , buttonText: {displayText: 'OWNER MENU'}, type: 1},
{buttonId: prefix + 'searchmenu' , buttonText: {displayText: 'SEARCH MENU'}, type: 1},
{buttonId: prefix + 'convertmenu' , buttonText: {displayText: 'CONVERT MENU'}, type: 1},
{buttonId: prefix + 'toolsmenu' , buttonText: {displayText: 'TOOLS MENU'}, type: 1},
{buttonId: prefix + 'othersmenu' , buttonText: {displayText: 'OTHERS MENU'}, type: 1},
{buttonId: prefix + 'moviemenu' , buttonText: {displayText: 'MOVIE MENU'}, type: 1},
{buttonId: prefix + 'aimenu' , buttonText: {displayText: 'AI MENU'}, type: 1},
{buttonId: prefix + 'logomenu' , buttonText: {displayText: 'LOGO MENU'}, type: 1},
{buttonId: prefix + 'mainmenu' , buttonText: {displayText: 'MAIN MENU'}, type: 1},
]
const buttonMessage = {
  image: config.IMAGE_PATH || config.IMAGE_PATH,
  caption: `*👋 Hello ${pushname}*

*╭━━━━━━━✧༺♥༻✧━━━━━━━*
*│◈ ᴏᴡɴᴇʀ : manaofc*
*│◈ ᴠᴇʀꜱɪᴏɴ : ${version}*
*│◈ ʀᴜɴᴛɪᴍᴇ : ${runtime(process.uptime())}*
*│◈ ʀᴀᴍ ᴜꜱᴀɢᴇ : ${(process.memoryUsage().heapUsed / 1024 / 1024).toFixed(2)}MB / ${Math.round(require('os').totalmem / 1024 / 1024)}MB*
*╰━━━━━━━✧༺♥༻✧━━━━━━━*
`,
  footer: config.FOOTER || config.FOOTER,
  buttons: buttons,
  headerType: 4
}
return await manaofc.buttonMessage(from, buttonMessage, mek)
} catch (e) {
reply('*Error !!*')
console.log(e)
}
})

// ============================================
// DOWNLOAD MENU - FIXED
// ============================================
cmd({
    pattern: "downmenu",
    react: "📥",
    dontAddCommandList: true,
    filename: __filename
},
async(manaofc, mek, m,{from, prefix, command, reply, config}) => {
try{
let menuc = `*📥 ${config.BOT_NAME || config.BOT_NAME} DOWNLOAD MENU. 📥*\n\n`
for (let i=0;i<commands.length;i++) { 
if(commands[i].category === 'download'){
  if(!commands[i].dontAddCommandList){
menuc += `*╭━━━━━━━✧༺♥༻✧━━━━━━━*
*╎🔖Command :* ${commands[i].pattern}
*╎🏷️Desc :* ${commands[i].desc}
*╎ 🧧Use:* ${commands[i].use}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n
`
}}};

let generatebutton = [{
    buttonId: `${prefix}ping`,
    buttonText: { displayText: 'GET BOT\'S PING' },
    type: 1
  }]
  let buttonMessaged = {
    image: config.IMAGE_PATH || config.IMAGE_PATH,
    caption: menuc,
    footer: config.FOOTER || config.FOOTER,
    headerType: 4,
    buttons: generatebutton
  };
  return await manaofc.buttonMessage(from, buttonMessaged, mek);
} catch (e) {
  reply('*ERROR !!*')
  console.log(e)
}
})

//=================================
//====== OWNER MENU ===============
//===================================

cmd({
  pattern: "ownermenu",
  react: "🗣️",
  dontAddCommandList: true,
  filename: __filename
},
async(manaofc, mek, m,{from, prefix, command, reply, config}) => {
try{
let menuc = `*🗣️ ${config.BOT_NAME || config.BOT_NAME} OWNER MENU. 🗣️*\n\n`
for (let i=0;i<commands.length;i++) { 
if(commands[i].category === 'owner'){
if(!commands[i].dontAddCommandList){
menuc += `*╭━━━━━━━✧༺♥༻✧━━━━━━━*
*╎🔖Command :* ${commands[i].pattern}
*╎🏷️Desc :* ${commands[i].desc}
*╎ 🧧Use:* ${commands[i].use}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n
`
}}};
let generatebutton = [{
    buttonId: `${prefix}ping`,
    buttonText: { displayText: 'GET BOT\'S PING' },
    type: 1
  }]
let buttonMessaged = {
  image: config.IMAGE_PATH || config.IMAGE_PATH,
  caption: menuc,
  footer: config.FOOTER || config.FOOTER,
  headerType: 4,
  buttons: generatebutton
};
return await manaofc.buttonMessage(from, buttonMessaged, mek);
} catch (e) {
reply('*ERROR !!*')
console.log(e)
}
})

// ============================================
// SEARCH MENU - FIXED
// ============================================
cmd({
    pattern: "searchmenu",
    react: "🔍",
    dontAddCommandList: true,
    filename: __filename
},
async(manaofc, mek, m,{from, prefix, command, reply, config}) => {
try{
let menuc = `*🔍 ${config.BOT_NAME || config.BOT_NAME} SEARCH MENU. 🔍*\n\n`
for (let i=0;i<commands.length;i++) { 
if(commands[i].category === 'search'){
  if(!commands[i].dontAddCommandList){
menuc += `*╭━━━━━━━✧༺♥༻✧━━━━━━━*
*╎🔖Command :* ${commands[i].pattern}
*╎🏷️Desc :* ${commands[i].desc}
*╎ 🧧Use:* ${commands[i].use}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n
`
}}};
let generatebutton = [{
    buttonId: `${prefix}ping`,
    buttonText: { displayText: 'GET BOT\'S PING' },
    type: 1
  }]
  let buttonMessaged = {
    image: config.IMAGE_PATH || config.IMAGE_PATH,
    caption: menuc,
    footer: config.FOOTER || config.FOOTER,
    headerType: 4,
    buttons: generatebutton
  };
  return await manaofc.buttonMessage(from, buttonMessaged, mek);
} catch (e) {
  reply('*ERROR !!*')
  console.log(e)
}
})
// ============================================
// CONVERT MENU
// ============================================
cmd({
    pattern: "convertmenu",
    react: "🔄",
    dontAddCommandList: true,
    filename: __filename
},
async(manaofc, mek, m,{from, prefix, command, reply, config}) => {
try{
let menuc = `*🔄 ${config.BOT_NAME || config.BOT_NAME} CONVERT MENU. 🔄*\n\n`
for (let i=0;i<commands.length;i++) { 
if(commands[i].category === 'convert'){
  if(!commands[i].dontAddCommandList){
menuc += `*╭━━━━━━━✧༺♥༻✧━━━━━━━*
*╎🔖Command :* ${commands[i].pattern}
*╎🏷️Desc :* ${commands[i].desc}
*╎ 🧧Use:* ${commands[i].use}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n
`
}}};
let generatebutton = [{
    buttonId: `${prefix}ping`,
    buttonText: { displayText: 'GET BOT\'S PING' },
    type: 1
  }]
  let buttonMessaged = {
    image: config.IMAGE_PATH || config.IMAGE_PATH,
    caption: menuc,
    footer: config.FOOTER || config.FOOTER,
    headerType: 4,
    buttons: generatebutton
  };
  return await manaofc.buttonMessage(from, buttonMessaged, mek);
} catch (e) {
  reply('*ERROR !!*')
  console.log(e)
}
})

// ============================================
// TOOLS MENU
// ============================================
cmd({
    pattern: "toolsmenu",
    react: "🔧",
    dontAddCommandList: true,
    filename: __filename
},
async(manaofc, mek, m,{from, prefix, command, reply, config}) => {
try{
let menuc = `*🔧 ${config.BOT_NAME || config.BOT_NAME} TOOLS MENU. 🔧*\n\n`
for (let i=0;i<commands.length;i++) { 
if(commands[i].category === 'tools'){
  if(!commands[i].dontAddCommandList){
menuc += `*╭━━━━━━━✧༺♥༻✧━━━━━━━*
*╎🔖Command :* ${commands[i].pattern}
*╎🏷️Desc :* ${commands[i].desc}
*╎ 🧧Use:* ${commands[i].use}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n
`
}}};
let generatebutton = [{
    buttonId: `${prefix}ping`,
    buttonText: { displayText: 'GET BOT\'S PING' },
    type: 1
  }]
  let buttonMessaged = {
    image: config.IMAGE_PATH || config.IMAGE_PATH,
    caption: menuc,
    footer: config.FOOTER || config.FOOTER,
    headerType: 4,
    buttons: generatebutton
  };
  return await manaofc.buttonMessage(from, buttonMessaged, mek);
} catch (e) {
  reply('*ERROR !!*')
  console.log(e)
}
})

// ============================================
// OTHERS MENU - FIXED
// ============================================
cmd({
    pattern: "othersmenu",
    react: "🎐",
    dontAddCommandList: true,
    filename: __filename
},
async(manaofc, mek, m,{from, prefix, command, reply, config}) => {
try{
let menuc = `*🎐 ${config.BOT_NAME || config.BOT_NAME} OTHER MENU. 🎐*\n\n`
for (let i=0;i<commands.length;i++) { 
if(commands[i].category === 'others'){
if(!commands[i].dontAddCommandList){
menuc += `*╭━━━━━━━✧༺♥༻✧━━━━━━━*
*╎🔖Command :* ${commands[i].pattern}
*╎🏷️Desc :* ${commands[i].desc}
*╎ 🧧Use:* ${commands[i].use}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n
`
}}};
let generatebutton = [{
    buttonId: `${prefix}ping`,
    buttonText: { displayText: 'GET BOT\'S PING' },
    type: 1
  }]
  let buttonMessaged = {
    image: config.IMAGE_PATH || config.IMAGE_PATH,
    caption: menuc,
    footer: config.FOOTER || config.FOOTER,
    headerType: 4,
    buttons: generatebutton
  };
  return await manaofc.buttonMessage(from, buttonMessaged, mek);
} catch (e) {
  reply('*ERROR !!*')
  console.log(e)
}
})

// ============================================
// MOVIE MENU - ALREADY OK, BUT DOUBLE CHECK
// ============================================
cmd({
  pattern: "moviemenu",
  react: "🎬",
  dontAddCommandList: true,
  filename: __filename
},
async(manaofc, mek, m,{from, prefix, command, reply, config}) => {
try{
let menuc = `*🎬 ${config.BOT_NAME || config.BOT_NAME} MOVIE MENU. 🎬*\n\n`
for (let i=0;i<commands.length;i++) { 
if(commands[i].category === 'movie'){
if(!commands[i].dontAddCommandList){
menuc += `*╭━━━━━━━✧༺♥༻✧━━━━━━━*
*╎🔖Command :* ${commands[i].pattern}
*╎🏷️Desc :* ${commands[i].desc}
*╎ 🧧Use:* ${commands[i].use}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n
`
}}};
let generatebutton = [{
    buttonId: `${prefix}ping`,
    buttonText: { displayText: 'GET BOT\'S PING' },
    type: 1
  }]
let buttonMessaged = {
  image: config.IMAGE_PATH || config.IMAGE_PATH,
  caption: menuc,
  footer: config.FOOTER || config.FOOTER,
  headerType: 4,
  buttons: generatebutton
};
return await manaofc.buttonMessage(from, buttonMessaged, mek);
} catch (e) {
reply('*ERROR !!*')
console.log(e)
}
})

// ============================================
// AI MENU
// ============================================
cmd({
    pattern: "aimenu",
    react: "🤖",
    dontAddCommandList: true,
    filename: __filename
},
async(manaofc, mek, m,{from, prefix, command, reply, config}) => {
try{
let menuc = `*🤖 ${config.BOT_NAME || config.BOT_NAME} AI MENU. 🤖*\n\n`
for (let i=0;i<commands.length;i++) { 
if(commands[i].category === 'ai'){
if(!commands[i].dontAddCommandList){
menuc += `*╭━━━━━━━✧༺♥༻✧━━━━━━━*
*╎🔖Command :* ${commands[i].pattern}
*╎🏷️Desc :* ${commands[i].desc}
*╎ 🧧Use:* ${commands[i].use}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n
`
}}};
let generatebutton = [{
    buttonId: `${prefix}ping`,
    buttonText: { displayText: 'GET BOT\'S PING' },
    type: 1
  }]
  let buttonMessaged = {
    image: config.IMAGE_PATH || config.IMAGE_PATH,
    caption: menuc,
    footer: config.FOOTER || config.FOOTER,
    headerType: 4,
    buttons: generatebutton
  };
  return await manaofc.buttonMessage(from, buttonMessaged, mek);
} catch (e) {
  reply('*ERROR !!*')
  console.log(e)
}
})

// ============================================
// LOGO MENU
// ============================================
cmd({
    pattern: "logomenu",
    react: "🎨",
    dontAddCommandList: true,
    filename: __filename
},
async(manaofc, mek, m,{from, prefix, command, reply, config}) => {
try{
let menuc = `*🎨 ${config.BOT_NAME || config.BOT_NAME} LOGO MENU. 🎨*\n\n`
for (let i=0;i<commands.length;i++) { 
if(commands[i].category === 'logo'){
if(!commands[i].dontAddCommandList){
menuc += `*╭━━━━━━━✧༺♥༻✧━━━━━━━*
*╎🔖Command :* ${commands[i].pattern}
*╎🏷️Desc :* ${commands[i].desc}
*╎ 🧧Use:* ${commands[i].use}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n
`
}}};
let generatebutton = [{
    buttonId: `${prefix}ping`,
    buttonText: { displayText: 'GET BOT\'S PING' },
    type: 1
  }]
  let buttonMessaged = {
    image: config.IMAGE_PATH || config.IMAGE_PATH,
    caption: menuc,
    footer: config.FOOTER || config.FOOTER,
    headerType: 4,
    buttons: generatebutton
  };
  return await manaofc.buttonMessage(from, buttonMessaged, mek);
} catch (e) {
  reply('*ERROR !!*')
  console.log(e)
}
})

// ============================================
// MAIN MENU
// ============================================
cmd({
    pattern: "mainmenu",
    react: "🏠",
    dontAddCommandList: true,
    filename: __filename
},
async(manaofc, mek, m,{from, prefix, command, reply, config}) => {
try{
let menuc = `*🏠 ${config.BOT_NAME || config.BOT_NAME} MAIN MENU. 🏠*\n\n`
for (let i=0;i<commands.length;i++) { 
if(commands[i].category === 'main'){
if(!commands[i].dontAddCommandList){
menuc += `*╭━━━━━━━✧༺♥༻✧━━━━━━━*
*╎🔖Command :* ${commands[i].pattern}
*╎🏷️Desc :* ${commands[i].desc}
*╎ 🧧Use:* ${commands[i].use}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n
`
}}};
let generatebutton = [{
    buttonId: `${prefix}ping`,
    buttonText: { displayText: 'GET BOT\'S PING' },
    type: 1
  }]
  let buttonMessaged = {
    image: config.IMAGE_PATH || config.IMAGE_PATH,
    caption: menuc,
    footer: config.FOOTER || config.FOOTER,
    headerType: 4,
    buttons: generatebutton
  };
  return await manaofc.buttonMessage(from, buttonMessaged, mek);
} catch (e) {
  reply('*ERROR !!*')
  console.log(e)
}
})

// system command
cmd({
    pattern: "system",
    react: "🎑",
    alias: ["os","cpu"],
    desc: "Check bot\'s system info",
    category: "main",
    use: '.system',
    filename: __filename
},
async(manaofc, mek, m,{from, reply, config}) => {
try{
  let totalStorage = Math.floor(os.totalmem() / 1024 / 1024) + 'MB'
  let freeStorage = Math.floor(os.freemem() / 1024 / 1024) + 'MB'
  let cpuModel = os.cpus()[0].model
  let cpuSpeed = os.cpus()[0].speed / 1000
  let cpuCount = os.cpus().length
  let hostname = os.hostname()

  let mes = `
*⚙️ ${config.BOT_NAME || config.BOT_NAME} SYSTEM INFO. ⚙️*

  ◈ *Owner*: manaofc
  ◈ *Version*: ${version}
  ◈ *Runtime*: ${runtime(process.uptime())}
  ◈ *Os Name*: ${hostname}
  ◈ *Total Ram*: ${totalStorage}
  ◈ *Free Ram*: ${freeStorage}
  ◈ *CPU Model*: ${cpuModel}
  ◈ *CPU Speed*: ${cpuSpeed} GHz
  ◈ *CPU Cores*: ${cpuCount} 
  
${config.FOOTER || config.FOOTER}`

await manaofc.sendMessage(from, { image: {url: config.IMAGE_PATH || config.IMAGE_PATH}, caption: mes }, { quoted: mek })
    
} catch (e) {
reply('*Error !!*')
console.log(e)
}
})

// main command
cmd({
    pattern: "ping",
    alias: ["speed", "pong"],
    use: '.ping',
    desc: "Check bot's response time.",
    category: "main",
    react: "⚡",
    filename: __filename
},
async (manaofc, mek, m, { from, quoted, sender, reply, config }) => {
    try {
        const start = Date.now();

        const reactionEmojis = ['🔥', '⚡', '🚀', '💨', '🎯', '🎉', '🌟', '💥', '🕐', '🔹'];
        const textEmojis = ['💎', '🏆', '⚡️', '🚀', '🎶', '🌠', '🌀', '🔱', '🛡️', '✨'];

        const reactionEmoji = reactionEmojis[Math.floor(Math.random() * reactionEmojis.length)];
        let textEmoji = textEmojis[Math.floor(Math.random() * textEmojis.length)];

        while (textEmoji === reactionEmoji) {
            textEmoji = textEmojis[Math.floor(Math.random() * textEmojis.length)];
        }

        await manaofc.sendMessage(from, {
            react: { text: textEmoji, key: mek.key }
        });

        const end = Date.now();
        const responseTime = end - start;

        const text = `${config.BOT_NAME || config.BOT_NAME}\n\n*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n🏓 *Pong!* ${reactionEmoji}\n⏱️ Response Time: *${responseTime} ms*\n*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n${config.FOOTER || config.FOOTER}`;

        await manaofc.sendMessage(from, {
            image: { url: config.IMAGE_PATH || config.IMAGE_PATH },
            caption: text
        }, { quoted: mek });

    } catch (e) {
        console.error("Error in ping command:", e);
        reply("An error occurred: " + e.message);
    }
});
// owner command 
cmd({
    pattern: "owner",
    desc: "Display owner contact information.",
    react: "🌝",
    use: ".owner",
    category: "main",
    filename: __filename
},
async (manaofc, mek, m, { from, reply }) => {
    try {
        const vcard = 
            'BEGIN:VCARD\n' +
            'VERSION:3.0\n' +
            'FN:MANAOFC\n' +
            'ORG:MANAOFC\n' +
            'TEL;type=CELL;type=VOICE;waid=94759934522:+94759934522\n' +
            'EMAIL:manishasasmith27@gmail.com\n' +
            'END:VCARD';

        await manaofc.sendMessage(from, { 
            contacts: { 
                displayName: "manaofc", 
                contacts: [{ vcard }] 
            },  
            quoted: mek 
        });
    } catch (e) {
        console.error(e);
        reply('⚠️ An error occurred while fetching owner information.');
    }
});

// ========== DOWNLOAD COMMANDS ==========
//============== IMAGE DOWNLOAD ===========
cmd({
    pattern: "pinterest",
    react: '🖼️',
    alias: ["pinterestdl"],
    desc: "Search for related pics on Pinterest.",
    category: "download",
    use: '.pinterest <query>',
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply, config }) => {
    try {
        if (!q) return await reply("*Please provide a search query!*");

        const res = await fetch('https://allstars-apis.vercel.app/pinterest?search=' + encodeURIComponent(q));
        const result = await res.json();
        
        const data = result.data;
        
        if (!data || data.length === 0) {
            return await reply("*No images found!*");
        }

        for (let i = 0; i < Math.min(data.length, 7); i++) {
            await manaofc.sendMessage(from, { 
                image: { url: data[i] }, 
                caption: config.FOOTER 
            }, { quoted: mek });
        }
    } catch (e) {
        await reply("*Error fetching images!*");
        console.log(e);
    }
});


/* ================== SONG SEARCH ================== */
cmd(
  {
    pattern: "song",
    react: "🎵",
    alias: ["music", "yt"],
    category: "download",
    use: ".song <Song Name or YouTube URL>",
    filename: __filename,
  },
  async (manaofc, mek, m, { from, prefix, q, reply, config }) => {
    try {
      if (!q) return reply("❌ *Please provide a song name or YouTube URL!*");

      const search = await yts(q);
      if (!search.videos || search.videos.length === 0) {
        return reply("⚠️ *No song results found!*");
      }

      const song = search.videos[0];

      const caption = `*🎶 ${config.BOT_NAME || config.BOT_NAME} SONG DOWNLOAD.📥*
      *╭━━━━━━━✧༺♥༻✧━━━━━━━*
      │✨ \`Title\` : ${song.title}
      │⏰ \`Duration\` : ${song.timestamp}
      │👀 \`Views\` : ${song.views}
      │ 📅 ‍ \`Uploaded\` : ${song.ago}
      │ 📺 ‍ \`Channel\` : ${song.author?.name || "Unknown"}
      *╰━━━━━━━✧༺♥༻✧━━━━━━━*`;

      const buttons = [
        {
          buttonId: `${prefix}yta ${song.url}`,
          buttonText: { displayText: "AUDIO TYPE 🎙" },
          type: 1,
        },
        {
          buttonId: `${prefix}ytd ${song.url}`,
          buttonText: { displayText: "DOCUMENT TYPE 📁" },
          type: 1,
        },
      ];

      const buttonMessage = {
        image: song.thumbnail,
        caption: caption,
        footer: config.FOOTER || config.FOOTER,
        buttons: buttons,
        headerType: 4,
      };

      await manaofc.buttonMessage(from, buttonMessage, mek );

    } catch (e) {
      console.log(e);
      reply("❌ *An error occurred while searching!*");
    }
  }
);
/* ================== AUDIO DOWNLOAD ================== */
cmd(
  {
    pattern: "yta",
    react: "⬇️",
    dontAddCommandList: true,
    filename: __filename,
  },
  async (manaofc, mek, m, { from, q, reply, config }) => {
    try {
      if (!q) return reply("❌ *Need a YouTube URL!*");

      await manaofc.sendMessage(from, {
        react: { text: "⬇️", key: mek.key },
      });

      const res = await fetch(
        "https://manaofc-api.vercel.app/yt/mp3?url=" + encodeURIComponent(q)
      );

      const yta = await res.json();

      if (!yta.status || !yta.download_url) {
        return reply("❌ *Failed to fetch audio!*");
      }

      await manaofc.sendMessage(
        from,
        {
          audio: { url: yta.download_url },
          mimetype: "audio/mpeg",
          ptt: false,
        },
        { quoted: mek }
      );

      await manaofc.sendMessage(from, {
        react: { text: "✔️", key: mek.key },
      });

    } catch (e) {
      console.log(e);
      reply("❌ *Audio download failed!*");
    }
  }
);

/* ================== DOCUMENT DOWNLOAD ================== */
cmd(
  {
    pattern: "ytd",
    react: "⬇️",
    dontAddCommandList: true,
    filename: __filename,
  },
  async (manaofc, mek, m, { from, q, reply, config }) => {
    try {
      if (!q) return reply("❌ *Need a YouTube URL!*");

      await manaofc.sendMessage(from, {
        react: { text: "⬇️", key: mek.key },
      });

      const res = await fetch(
        "https://manaofc-api.vercel.app/yt/mp3?url=" + encodeURIComponent(q)
      );


      const yta = await res.json();

      if (!yta.status || !yta.download_url) {
        return reply("❌ *Failed to fetch document link!*");
      }

      await manaofc.sendMessage(
        from,
        {
          document: { url: yta.download_url },
          mimetype: "audio/mpeg",
          fileName: yta.title + ".mp3",
          caption: "🎵 *" + yta.title + "*",
        },
        { quoted: mek }
      );

      await manaofc.sendMessage(from, {
        react: { text: "✔️", key: mek.key },
      });

    } catch (e) {
      console.log(e);
      reply("❌ *Document download failed!*");
    }
  }
);
/* ================== VIDEO SEARCH ================== */
cmd(
{
pattern: "video",
react: "🎦",
alias: ["ytmp4"],
category: "download",
use: ".video <Video Name or YouTube URL>",
filename: __filename,
},
async (manaofc, mek, m, { from, prefix, q, reply, config }) => {
try {
if (!q) return reply("❌ Please provide a song name or YouTube URL!");
const search = await yts(q);
if (!search.videos || search.videos.length === 0) {
return reply("⚠️ No video results found!");
}
const video = search.videos[0];
const caption = `*🎦 ${config.BOT_NAME || config.BOT_NAME} VIDEO DOWNLOAD.📥* *╭━━━━━━━✧༺♥༻✧━━━━━━━* │✨ \`Title\` : ${video.title}
│⏰ \`Duration\` : ${video.timestamp}
│👀 \`Views\` : ${video.views}
│ 📅 ‍ \`Uploaded\` : ${video.ago}
│ 📺 ‍ \`Channel\` : ${video.author?.name || "Unknown"}
╰━━━━━━━✧༺♥༻✧━━━━━━━`;
const buttons = [
{
buttonId: `${prefix}ytq ${video.url}`,
buttonText: { displayText: "VIDEO QUALITY 📊" },
type: 1,
}
];
const buttonMessage = {
image: video.thumbnail,
caption: caption,
footer: config.FOOTER || config.FOOTER,
buttons: buttons,
headerType: 4,
};
await manaofc.buttonMessage(from, buttonMessage, mek );
} catch (e) {
console.log(e);
reply("❌ An error occurred while searching!");
}
}
);

/* ================== VIDEO DOWNLOAD (Quality Selector) ================== */
cmd(
{
  pattern: "ytq",
  react: "📹",
  dontAddCommandList: true,
  filename: __filename,
},
async (manaofc, mek, m, { from, prefix, q, reply, config }) => {
  try {
    if (!q) return reply("❌ Need a YouTube URL!");
    
    // Get video ID from YouTube URL
    let videoId = "";
    const patterns = [
      /(?:youtube\.com\/watch\?v=|youtu\.be\/|youtube\.com\/embed\/)([^&\s?]+)/,
      /youtube\.com\/shorts\/([^&\s?]+)/,
    ];
    for (const p of patterns) {
      const match = q.match(p);
      if (match) { videoId = match[1]; break; }
    }
    
    const thumbnail = videoId ? `https://i.ytimg.com/vi/${videoId}/maxresdefault.jpg` : null;
    
    // Show thumbnail
    if (thumbnail) {
      await manaofc.sendMessage(from, {
        image: { url: thumbnail },
        caption: `*🎬 Video Found!*\n\n🔗 ${q}\n\n👇 *Select the quality you need:*`,
      }, { quoted: mek });
    }
    
    // Quality list message
    const qualities = [
      { q: "144", title: "144p 🥔", desc: "Low quality, small size" },
      { q: "360", title: "360p 📱", desc: "Standard quality" },
      { q: "480", title: "480p 💻", desc: "Good quality" },
      { q: "720", title: "720p 🖥️", desc: "HD quality" },
      { q: "1080", title: "1080p 🎬", desc: "Full HD quality" },
    ];
    
    const listMessage = {
      text: thumbnail ? "*👇 Select quality:*" : `*🎬 Video Downloader*\n\n🔗 ${q}\n\n*👇 Select quality:*`,
      footer: config.FOOTER || config.FOOTER,
      title: "*📥 Quality Selector*",
      buttonText: "View Qualities 📊",
      sections: [{
        title: "Available Qualities",
        rows: qualities.map(item => ({
          title: item.title,
          rowId: `${prefix}ytvdl ${q}|${item.q}`,
          description: item.desc,
        })),
      }],
    };
    
    await manaofc.listMessage(from, listMessage, mek);
    
  } catch (e) {
    console.log(e);
    reply("❌ *Error showing quality options!*");
  }
}
);

/* ================== VIDEO DOWNLOAD (Actual Download) ================== */
cmd(
{
  pattern: "ytvdl",
  react: "⬇️",
  dontAddCommandList: true,
  filename: __filename,
},
async (manaofc, mek, m, { from, q, reply, config }) => {
  try {
    if (!q || !q.includes("|")) {
      return reply("❌ Invalid format! Use: .ytdl <url>|<quality>");
    }
    
    const parts = q.split("|");
    const url = parts[0];
    const quality = parts[1];
    
    if (!url || !quality) {
      return reply("❌ Invalid format! Use: .ytdl <url>|<quality>");
    }
    
    await manaofc.sendMessage(from, {
      react: { text: "⬇️", key: mek.key },
    });
    
    // Send a request to the API
    const res = await fetch(
      `https://manaofc-api.vercel.app/yt/mp4?url=${encodeURIComponent(url)}&quality=${quality}`
    );
    
    const ytd = await res.json();
    
    if (!ytd.status || !ytd.download_url) {
      return reply("❌ *Failed to fetch video!*\n\nCannot get video for this quality. Try another quality.");
    }
    
    // Send video (inline video)
    await manaofc.sendMessage(
      from,
      {
        video: { url: ytd.download_url },
        mimetype: "video/mp4",
        caption: `*🎬 ${ytd.title || "Video"}*\n📊 Quality: ${quality}p\n✅ Downloaded via ${config.BOT_NAME || config.BOT_NAME}`,
      },
      { quoted: mek }
    );
    
    // ✅ Add reaction
    await manaofc.sendMessage(from, {
      react: { text: "✔️", key: mek.key },
    });
    
  } catch (e) {
    console.log(e);
    reply("❌ *Video download failed!*");
  }
}
);

/* ================== FACEBOOK VIDEO DOWNLOADER ================== */
cmd(
  {
    pattern: "fb",
    react: "📘",
    alias: ["facebook", "fbdl"],
    category: "download",
    use: ".fb <Facebook Video URL>",
    filename: __filename,
  },
  async (manaofc, mek, m, { from, q, reply }) => {
    try {
      if (!q) return reply("❌ *Need a Facebook URL!*");

      await manaofc.sendMessage(from, {
        react: { text: "⬇️", key: mek.key },
      });

      // ✅ නිවැරදි API URL එක
      const res = await fetch(
        `https://apis.davidcyriltech.my.id/facebook?url=${encodeURIComponent(q)}`
      );

      const json = await res.json();

      // ✅ නිවැරදි response structure එක
      if (!json.success || !json.result?.downloads) {
        return reply("❌ *Failed to fetch video!*");
      }

      const fb = json.result;
      const hdUrl = fb.downloads?.hd?.url;
      const sdUrl = fb.downloads?.sd?.url;

      // 📈 පළමුව HD quality එක යවනවා
      if (hdUrl) {
        await manaofc.sendMessage(
          from,
          {
            video: { url: hdUrl },
            caption: `📈 *HD Quality*\n📘 *${fb.title?.replace(/\r\n/g, " ") || "Facebook Video"}*`,
          },
          { quoted: mek }
        );
      }
      // 📉 HD නැත්නම් SD quality එකට fallback වෙනවා
      else if (sdUrl) {
        await manaofc.sendMessage(
          from,
          {
            video: { url: sdUrl },
            caption: `📉 *SD Quality*\n📘 *${fb.title?.replace(/\r\n/g, " ") || "Facebook Video"}*`,
          },
          { quoted: mek }
        );
      } else {
        return reply("❌ *No download links found!*");
      }

      await manaofc.sendMessage(from, {
        react: { text: "✔️", key: mek.key },
      });

    } catch (e) {
      console.log(e);
      reply("❌ *HD video download failed!*");
    }
  }
);


/* ================== TIKTOK COMMAND ================== */
cmd(
  {
    pattern: "tiktok",
    react: "🎵",
    alias: ["tt", "tik"],
    category: "download",
    use: ".tiktok <TikTok URL>",
    filename: __filename,
  },
  async (manaofc, mek, m, { from, prefix, q, reply, config }) => {
    try {
      if (!q) return reply("❌ *Please provide a TikTok URL!*");

      const apiUrl = `https://api-aswin-sparky.koyeb.app/api/downloader/tiktok?url=${encodeURIComponent(q)}`;
      const res = await fetch(apiUrl);
      const data = await res.json();

      if (!data.status || !data.data) {
        return reply("⚠️ *Failed to fetch TikTok video!*");
      }

      const tt = data.data;

      const caption = `*🎵 ${config.BOT_NAME || config.BOT_NAME} TIKTOK DOWNLOAD.📥*
      *╭━━━━━━━✧༺♥༻✧━━━━━━━*
      │✨ \`Title\` : ${tt.title || "No title"}
      │👤 \`Author\` : ${tt.author?.nickname || "Unknown"}
      │⏰ \`Duration\` : ${tt.duration || "N/A"}s
      │👀 \`Views\` : ${tt.view || 0}
      │💬 \`Comments\` : ${tt.comment || 0}
      │▶️ \`Plays\` : ${tt.play || 0}
      │🔗 \`Shares\` : ${tt.share || 0}
      *╰━━━━━━━✧༺♥༻✧━━━━━━━*`;

      const buttons = [
        {
          buttonId: `${prefix}ttv ${q}`,
          buttonText: { displayText: "VIDEO TYPE 🎥" },
          type: 1,
        },
        {
          buttonId: `${prefix}tta ${q}`,
          buttonText: { displayText: "AUDIO TYPE 🎙" },
          type: 1,
        },
      ];

      const buttonMessage = {
        image: tt.thumbnail,
        caption: caption,
        footer: config.FOOTER || config.FOOTER,
        buttons: buttons,
        headerType: 4,
      };

      await manaofc.buttonMessage(from, buttonMessage, mek);

    } catch (e) {
      console.log(e);
      reply("❌ *An error occurred while fetching TikTok video!*");
    }
  }
);

/* ================== TIKTOK VIDEO DOWNLOAD ================== */
cmd(
  {
    pattern: "ttv",
    react: "⬇️",
    dontAddCommandList: true,
    filename: __filename,
  },
  async (manaofc, mek, m, { from, q, reply }) => {
    try {
      if (!q) return reply("❌ *Need a TikTok URL!*");

      await manaofc.sendMessage(from, {
        react: { text: "⬇️", key: mek.key },
      });

      const res = await fetch(
        `https://api-aswin-sparky.koyeb.app/api/downloader/tiktok?url=${encodeURIComponent(q)}`
      );

      const data = await res.json();

      if (!data.status || !data.data?.video) {
        return reply("❌ *Failed to fetch video!*");
      }

      await manaofc.sendMessage(
        from,
        {
          video: { url: data.data.video },
          caption: `🎥 *${data.data.title || "TikTok Video"}*`,
        },
        { quoted: mek }
      );

      await manaofc.sendMessage(from, {
        react: { text: "✔️", key: mek.key },
      });

    } catch (e) {
      console.log(e);
      reply("❌ *Video download failed!*");
    }
  }
);

/* ================== TIKTOK AUDIO DOWNLOAD ================== */
cmd(
  {
    pattern: "tta",
    react: "⬇️",
    dontAddCommandList: true,
    filename: __filename,
  },
  async (manaofc, mek, m, { from, q, reply }) => {
    try {
      if (!q) return reply("❌ *Need a TikTok URL!*");

      await manaofc.sendMessage(from, {
        react: { text: "⬇️", key: mek.key },
      });

      const res = await fetch(
        `https://api-aswin-sparky.koyeb.app/api/downloader/tiktok?url=${encodeURIComponent(q)}`
      );

      const data = await res.json();

      if (!data.status || !data.data?.audio) {
        return reply("❌ *Failed to fetch audio!*");
      }

      await manaofc.sendMessage(
        from,
        {
          audio: { url: data.data.audio },
          mimetype: "audio/mpeg",
          ptt: false,
        },
        { quoted: mek }
      );

      await manaofc.sendMessage(from, {
        react: { text: "✔️", key: mek.key },
      });

    } catch (e) {
      console.log(e);
      reply("❌ *Audio download failed!*");
    }
  }
);

// ============================================
// MEGA DOWNLOAD COMMAND
// ============================================



// ============================================
// AN1 SEARCH COMMAND
// ============================================
cmd(
  {
    pattern: "an1",
    react: "🎮",
    alias: ["mod", "an1search"],
    category: "download",
    use: ".an1 *<App Name>*",
    filename: __filename,
  },
  async (manaofc, mek, m, { from, prefix, q, reply, config }) => {
    try {
      if (!q) return await reply("*Please provide a game/app name!*\n\nExample: `.an1 freefire`");

      await manaofc.sendMessage(from, { react: { text: "🔍", key: mek.key } });

      const response = await fetch(
        "https://manaofc-api.vercel.app/an1/search?q=" + encodeURIComponent(q)
      );

      const res = await response.json();

      if (!res.results || res.results.length < 1) {
        return await reply("*❌ No results found on AN1!*");
      }

      const data = res.results;

      const rows = data.slice(0, 10).map((v) => ({
        buttonId: prefix + "dan1 " + v.link,
        buttonText: { 
          displayText: v.title.length > 30 ? "🎮 " + v.title.slice(0, 27) + "..." : "🎮 " + v.title 
        },
        type: 1,
      }));

      const buttonMessage = {
        image: config.IMAGE_PATH || config.IMAGE_PATH,
        caption: `*🔰 ${config.BOT_NAME || config.BOT_NAME} AN1 SEARCH*`,
        footer: config.FOOTER || config.FOOTER,
        buttons: rows,
        headerType: 4,
      };

      return await manaofc.buttonMessage(from, buttonMessage, mek);

    } catch (e) {
      console.error(e);
      await reply("*ERROR !!* " + e.message);
    }
  }
);

// ============================================
// DAN1 DOWNLOAD COMMAND (AUTO DOCUMENT SEND)
// ============================================
cmd(
  {
    pattern: "dan1",
    react: "📥",
    dontAddCommandList: true,
    filename: __filename,
  },
  async (manaofc, mek, m, { from, q, reply, config }) => {
    try {
      if (!q) return await reply("*❌ Please provide an AN1 URL!*");

      await manaofc.sendMessage(from, { react: { text: "⬇️", key: mek.key } });

      const response = await fetch(
        "https://manaofc-api.vercel.app/an1/download?url=" + encodeURIComponent(q)
      );

      const app = await response.json();

      if (!app.directDownloadUrl) {
        return await reply("*❌ Download link not available!*\n\n*Error:* " + (app.message || "Unknown error"));
      }

      await manaofc.sendMessage(from, {
        image: { url: app.icon },
        caption: "*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n*📦 Downloading " + app.title + "...*\n\n" +
          "*Version:* " + app.version + "\n" +
          "*Size:* " + app.size + "\n" +
          "*Developer:* " + app.developer + "\n" +
          "*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n" +
          "⏳ *Sending APK file...*"
      }, { quoted: mek });

      await delay(1000);

      await manaofc.sendMessage(from, {
        document: { url: app.directDownloadUrl },
        mimetype: "application/vnd.android.package-archive",
        fileName: app.title.replace(/[^a-zA-Z0-9]/g, "_") + "_v" + app.version + ".apk",
        caption: `${config.FOOTER || config.FOOTER}`
      }, { quoted: mek });

      await manaofc.sendMessage(from, { react: { text: "✅", key: mek.key } });

    } catch (e) {
      console.error(e);
      await reply("*❌ ERROR !!*\n\n" + e.message);
    }
  }
);

// ========== XNXX DOWNLOAD ==========
const BASE_LINK = "https://manaofc-api.vercel.app";

cmd({
    pattern: "xnxx",
    desc: "Download XNXX Video",
    use: ".xnxx <query>",
    react: "🔞",
    category: "download",
    filename: __filename
},
async (manaofc, mek, m, { from, prefix, q, reply, config }) => {
    try {
        if (!q) return reply("*Please enter a query!*");

        const response = await fetch(
            BASE_LINK + "/xnxx/search?q=" + encodeURIComponent(q));

        const res = await response.json();

        if (!res.status || !res.result || res.result.length < 1) {
            return reply("*❌ No results found!*");
        }

        const rows = res.result.slice(0, 10).map((v) => ({
            buttonId: prefix + "xnxxvid " + v.url,
            buttonText: {
                displayText:
                    v.title.length > 40
                        ? v.title.slice(0, 37) + "..."
                        : v.title
            },
            type: 1
        }));

        const buttonMessage = {
            image: "https://files.catbox.moe/rnn9bf.jpeg",
            caption: `*🔞 ${config.BOT_NAME || config.BOT_NAME} XNXX SEARCH*`,
            footer: config.FOOTER || config.FOOTER,
            buttons: rows,
            headerType: 4
        };

        await manaofc.buttonMessage(from, buttonMessage, mek);

    } catch (e) {
        console.log(e);
        reply("*❌ Error occurred!*");
    }
});

cmd({
    pattern: "xnxxvid",
    react: "⬇️",
    dontAddCommandList: true,
    filename: __filename
},
async (manaofc, mek, m, { from, q, reply, config }) => {
    try {
        if (!q) return reply("*Need a video url!*");

        const response = await fetch(
            BASE_LINK + "/xnxx/details?url=" + encodeURIComponent(q)
        );

        const res = await response.json();

        if (!res.status || !res.result) {
            return reply("*❌ Failed to fetch video!*");
        }

        const data = res.result;

        let caption = "*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n*🔞 XNXX VIDEO DOWNLOAD*\n🎬 Title: " + data.title + "\n⏱ Duration: " + data.duration + "\n👀 Views: " + data.views + "\n👍 Likes: " + data.likes + "\n⭐ Rating: " + data.rating + "\n💬 Comments: " + data.comments + "\n*╰━━━━━━━✧༺♥༻✧━━━━━━━*";

        await manaofc.sendMessage(from, {
            image: { url: data.thumbnail },
            caption
        }, { quoted: mek });

        await manaofc.sendMessage(from, {
            video: { url: data.dlink },
            mimetype: "video/mp4"
        }, { quoted: mek });

    } catch (e) {
        console.log(e);
        reply("*❌ Download failed!*");
    }
});
//=============================================
// XVIDEO DOWNLOAD
//=============================================
cmd({
    pattern: "xvideo",
    desc: "Search and download XVIDEO",
    use: ".xvideo <query>",
    react: "🔞",
    category: "download",
    filename: __filename
},
async (manaofc, mek, m, { from, prefix, q, reply, config }) => {
    try {
        if (!q) return reply("❌ Please enter a search query!\n\nExample: `.xvideo mom and son`");

        const response = await fetch(
            `https://manaofc-api.vercel.app/xvideos/search?q=${encodeURIComponent(q)}`
        );

        const res = await response.json();

        // FIX 1: res.success -> res.status
        // FIX 2: res.results -> res.result
        if (!res.status || !res.result || res.result.length < 1) {
            return reply("*❌ No results found!*");
        }

        const rows = res.result.slice(0, 10).map((v) => {
            const displayTitle = v.title && v.title.length > 40 
                ? v.title.slice(0, 37) + "..." 
                : (v.title || "Unknown");
            
            // FIX: Handle empty URL gracefully
            const videoUrl = v.url || v.link || "";
            
            return {
                buttonId: `${prefix}xvdo ${videoUrl}`,
                buttonText: { displayText: displayTitle },
                type: 1
            };
        });

        const buttonMessage = {
            image: "https://files.catbox.moe/97o88i.png",
            caption: `*🔞 ${config.BOT_NAME || config.BOT_NAME} XVIDEO SEARCH`,
            footer: config.FOOTER || config.FOOTER,
            buttons: rows,
            headerType: 4
        };

        await manaofc.buttonMessage(from, buttonMessage, mek);

    } catch (e) {
        console.error("XVIDEO Search Error:", e);
        reply("*❌ Error occurred while searching!*");
    }
});

cmd({
    pattern: "xvdo",
    react: "⬇️",
    dontAddCommandList: true,
    filename: __filename
},
async (manaofc, mek, m, { from, q, reply, config }) => {
    try {
        if (!q) return reply("❌ Need a video URL!\n\nUse `.xvideo <query>` first.");

        await reply("⬇️ *Downloading video...*");

        const response = await fetch(
            `https://manaofc-api.vercel.app/xvideos/download?url=${encodeURIComponent(q)}`
        );

        const res = await response.json();

        // FIX 3: res.success -> res.status
        if (!res.status || !res.result) {
            return reply("*❌ Failed to fetch video details!*");
        }

        const data = res.result;

        // FIX 4: Removed likes, dislikes, size (not in API response)
        // FIX 5: Use data.dlink or data.url instead of data.download_url
        let caption = `*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n` +
                      `*🔞 XVIDEO DOWNLOAD*\n` +
                      `🎬 *Title:* ${data.title || "N/A"}\n` +
                      `👀 *Views:* ${data.views || "N/A"}\n` +
                      `⏱️ *Duration:* ${data.duration || "N/A"}\n` +
                      `*╰━━━━━━━✧༺♥༻✧━━━━━━━*`;

        // Send thumbnail with info
        if (data.thumbnail) {
            await manaofc.sendMessage(from, {
                image: { url: data.thumbnail },
                caption: caption
            }, { quoted: mek });
        } else {
            await reply(caption);
        }

        // FIX 6: Use data.dlink (primary) or data.url (fallback) instead of data.download_url
        const downloadUrl = data.dlink || data.url || null;

        if (downloadUrl) {
            await manaofc.sendMessage(from, {
                video: { url: downloadUrl },
                mimetype: "video/mp4",
                caption: `📥 *Download Complete*`
            }, { quoted: mek });
        } else {
            reply("*❌ Download URL not available!*\n\nVideo details fetched but download link is empty.");
        }

    } catch (e) {
        console.error("XVIDEO Download Error:", e);
        reply("*❌ Download failed! Please try again.*");
    }
});

// ============================================
// SINHALASUB SEARCH 
// ============================================

cmd(
  {
    pattern: "sinhalasub",
    react: "🎬",
    alias: ["ssub", "ssubsearch"],
    category: "movie",
    use: ".sinhalasub <movie name>",
    filename: __filename,
  },
  async (manaofc, mek, m, { from, prefix, q, reply, config }) => {
    try {
      if (!q) return reply("❌ *Please provide a movie name!*\n\n*Example:* .sinhalasub avatar");

      await manaofc.sendMessage(from, {
        react: { text: "🔍", key: mek.key },
      });

      const api = await fetch("https://manaofc-api.vercel.app/sinhalasub/search?q=" + encodeURIComponent(q));

      const res = await api.json();

      if (!res.status || !res.data || res.data.length === 0) {
        return reply("❌ *No movies found for your search!*");
      }

      const rows = res.data.slice(0, 10).map((v) => ({
        buttonId: prefix + "ssinfo " + v.url,
        buttonText: {
          displayText: v.title.length > 40 ? v.title.slice(0, 37) + "..." : v.title
        },
        type: 1
      }));

      const buttonMessage = {
        image: "https://files.catbox.moe/nsshzm.jpeg",
        caption: `*🎬 ${config.BOT_NAME || config.BOT_NAME} SINHALASUB SEARCH* `,
        footer: config.FOOTER || config.FOOTER,
        buttons: rows,
        headerType: 4
      };

      await manaofc.buttonMessage(from, buttonMessage, mek);

      await manaofc.sendMessage(from, {
        react: { text: "✅", key: mek.key },
      });

    } catch (e) {
      console.log(e);
      reply("❌ *An error occurred while searching!*");
    }
  }
);

// ============================================
// SINHALASUB INFO 
// ============================================

cmd(
  {
    pattern: "ssinfo",
    react: "📋",
    dontAddCommandList: true,
    filename: __filename,
  },
  async (manaofc, mek, m, { from, prefix, q, reply, config }) => {
    try {
      if (!q) return reply("❌ *Need a movie link!*");

      await manaofc.sendMessage(from, {
        react: { text: "⏳", key: mek.key },
      });

      const api = await fetch("https://manaofc-api.vercel.app/sinhalasub/info?url=" + encodeURIComponent(q));
      const res = await api.json();

      if (!res.status || !res.data) {
        return reply("❌ *Failed to get movie info!*");
      }

      const data = res.data;
      
      const caption = `*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n*🎬 ${data.title}*\n\n` +
                `*📅 Year:* ${data.year || "N/A"}\n` +
                `*⏱️ Duration:* ${data.duration || "N/A"}\n` +
                `*⭐ IMDB:* ${data.imdb || "N/A"}\n` +
                `*🗣️ Language:* ${data.language || "N/A"}\n` +
                `*🌍 Country:* ${data.country || "N/A"}\n` +
                `*🎬 Directors:* ${(Array.isArray(data.directors) ? data.directors.join(", ") : data.directors) || "N/A"}\n` +
                `*🌟 Stars:* ${(Array.isArray(data.stars) ? data.stars.join(", ") : data.stars) || "N/A"}\n` +
                `*🎞️ Genres:* ${(Array.isArray(data.genres) ? data.genres.join(", ") : data.genres) || "N/A"}\n` +
                `*╰━━━━━━━✧༺♥༻✧━━━━━━━*`;
      
      const buttons = data.links.map((dl) => ({
        buttonId: prefix + "ssdown " + dl.pageLink,
        buttonText: { displayText: dl.quality + " (" + dl.size + ")" },
        type: 1
      }));

      const buttonMessage = {
        image: data.thumbnail,
        caption: caption,
        footer: config.FOOTER || config.FOOTER,
        buttons: buttons,
        headerType: 4
      };

      await manaofc.buttonMessage(from, buttonMessage, mek);

      await manaofc.sendMessage(from, {
        react: { text: "✅", key: mek.key },
      });

    } catch (e) {
      console.log(e);
      reply("❌ *Failed to get movie info!*");
    }
  }
);

// ============================================
// SINHALASUB DOWNLOAD 
// ============================================

cmd(
  {
    pattern: "ssdown",
    react: "📁",
    dontAddCommandList: true,
    filename: __filename,
  },
  async (manaofc, mek, m, { from, q, reply, config }) => {
    try {
      if (!q) return reply("❌ *Need a download link!*");

      await manaofc.sendMessage(from, {
        react: { text: "⬇️", key: mek.key },
      });

      const api = await fetch("https://manaofc-api.vercel.app/sinhalasub/download?url=" + encodeURIComponent(q));
      const res = await api.json();

      if (!res.status || !res.data) {
        return reply("❌ *Failed to get download link!*");
      }

      const data = res.data;
      const downloadUrl = data.directUrl || data.pixeldrainUrl;

      await manaofc.sendMessage(
        from,
        {
          document: { url: downloadUrl },
          mimetype: "video/mp4",
          fileName: data.title + ".mp4",
        },
        { quoted: mek }
      );

      await manaofc.sendMessage(from, {
        react: { text: "✅", key: mek.key },
      });

    } catch (e) {
      console.log(e);
      reply("❌ *Download failed!*");
    }
  }
);
// ============================================
// CINESUBZ SEARCH 
// ============================================

cmd(
  {
    pattern: "cinesubz",
    react: "🎬",
    alias: ["cs", "movie"],
    category: "movie",
    use: ".cinesubz <movie name>",
    filename: __filename,
  },
  async (manaofc, mek, m, { from, prefix, q, reply, config }) => {
    try {
      if (!q) return reply("❌ *Please provide a movie name!*\n\n*Example:* .cinesubz deadpool");

      await manaofc.sendMessage(from, {
        react: { text: "🔍", key: mek.key },
      });

      const api = await fetch("https://api-dark-shan-yt.koyeb.app/movie/cinesubz-search?q=" + encodeURIComponent(q) + "&apikey=afb95c4d7db5cd8a" );

      const res = await api.json();

      if (!res.status || !res.data || res.data.length === 0) {
        return reply("❌ *No movies found for your search!*");
      }

      const rows = res.data.slice(0, 10).map((v) => ({
        buttonId: prefix + "cinfo " + v.link,
        buttonText: {
          displayText: v.title.length > 40 ? v.title.slice(0, 37) + "..." : v.title
        },
        type: 1
      }));

      const buttonMessage = {
        image: "https://files.catbox.moe/57a24d.jpeg",
        caption: `*🎬 ${config.BOT_NAME || config.BOT_NAME} CINESUBZ SEARCH* `,
        footer: config.FOOTER || config.FOOTER,
        buttons: rows,
        headerType: 4
      };

      await manaofc.buttonMessage(from, buttonMessage, mek);

      await manaofc.sendMessage(from, {
        react: { text: "✅", key: mek.key },
      });

    } catch (e) {
      console.log(e);
      reply("❌ *An error occurred while searching!*");
    }
  }
);

// ============================================
// CINESUBZ INFO 
// ============================================

cmd(
  {
    pattern: "cinfo",
    react: "📋",
    dontAddCommandList: true,
    filename: __filename,
  },
  async (manaofc, mek, m, { from, prefix, q, reply, config }) => {
    try {
      if (!q) return reply("❌ *Need a movie link!*");

      await manaofc.sendMessage(from, {
        react: { text: "⏳", key: mek.key },
      });

      const api = await fetch("https://api-dark-shan-yt.koyeb.app/movie/cinesubz-info?url=" + encodeURIComponent(q) + "&apikey=afb95c4d7db5cd8a" );

      const res = await api.json();

      if (!res.status || !res.data) {
        return reply("❌ *Failed to get movie info!*");
      }

      const data = res.data;
      
      const caption = `*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n*🎬 ${data.title}*\n\n` +
                `*📅 Year:* ${data.year || "N/A"}\n` +
                `*⏱️ Duration:* ${data.duration || "N/A"}\n` +
                `*⭐ Rating:* ${data.rating || "N/A"}\n` +
                `*🎞️ Quality:* ${data.quality || "N/A"}\n` +
                `*🗣️ Language:* ${data.tag || "N/A"}\n` +
                `*🌍 Country:* ${data.country || "N/A"}\n` +
                `*🎬 Directors:* ${(data.directors || "N/A").replace("Director:", "")}\n` +
                `*🌟 Stars:* ${data.stars || "N/A"}\n` +
                `*╰━━━━━━━✧༺♥༻✧━━━━━━━*`;
      
      const buttons = data.downloads.map((dl) => ({
        buttonId: prefix + "cdown " + dl.link,
        buttonText: { displayText: dl.quality + " (" + dl.size + ")" },
        type: 1
      }));

      const buttonMessage = {
        image: data.image,
        caption: caption,
        footer: config.FOOTER || config.FOOTER,
        buttons: buttons,
        headerType: 4
      };

      await manaofc.buttonMessage(from, buttonMessage, mek);

      await manaofc.sendMessage(from, {
        react: { text: "✅", key: mek.key },
      });

    } catch (e) {
      console.log(e);
      reply("❌ *Failed to get movie info!*");
    }
  }
);

// ============================================
// CINESUBZ DOWNLOAD 
// ============================================

cmd(
  {
    pattern: "cdown",
    react: "📁",
    dontAddCommandList: true,
    filename: __filename,
  },
  async (manaofc, mek, m, { from, q, reply, config }) => {
    try {
      if (!q) return reply("❌ *Need a download link!*");

      await manaofc.sendMessage(from, {
        react: { text: "⬇️", key: mek.key },
      });

      const api = await fetch("https://api-dark-shan-yt.koyeb.app/movie/cinesubz-download?url=" + encodeURIComponent(q) + "&apikey=afb95c4d7db5cd8a" );
      const res = await api.json();

      if (!res.status || !res.data || !res.data.download || res.data.download.length === 0) {
        return reply("❌ *Failed to get download link!*");
      }

      const data = res.data;
      const downloadUrl = data.download[0].url;

      await manaofc.sendMessage(
        from,
        {
          document: { url: downloadUrl },
          mimetype: "video/mp4",
          fileName: data.title,
        },
        { quoted: mek }
      );

      await manaofc.sendMessage(from, {
        react: { text: "✅", key: mek.key },
      });

    } catch (e) {
      console.log(e);
      reply("❌ *Download failed!*");
    }
  }
);

// ============================================
// SINHALACARTOONS SEARCH
// ============================================

cmd(
  {
    pattern: "sinhalacartoons",
    react: "📺",
    alias: ["sc", "cartoon"],
    category: "movie",
    use: ".sinhalacartoons <cartoon name>",
    filename: __filename,
  },
  async (manaofc, mek, m, { from, prefix, q, reply, config }) => {
    try {
      if (!q) return reply("❌ *Please provide a cartoon name!*\n\n*Example:* .sinhalacartoons smurfs");

      await manaofc.sendMessage(from, {
        react: { text: "🔍", key: mek.key },
      });

      const api = await fetch("https://manaofc-api.vercel.app/sinhalacartoons/search?q=" + encodeURIComponent(q));
      const res = await api.json();

      if (!res.results || res.results.length === 0) {
        return reply("❌ *No cartoons found for your search!*");
      }

      const rows = res.results.slice(0, 10).map((v) => ({
        buttonId: prefix + "scinfo " + v.link,
        buttonText: {
          displayText: v.title.length > 40 ? v.title.slice(0, 37) + "..." : v.title
        },
        type: 1
      }));

      const buttonMessage = {
        image: "https://files.catbox.moe/z2u40j.png",
        caption: `*📺 ${config.BOT_NAME || config.BOT_NAME} SINHALACARTOONS SEARCH*`,
        footer: config.FOOTER || config.FOOTER,
        buttons: rows,
        headerType: 4
      };

      await manaofc.buttonMessage(from, buttonMessage, mek);

      await manaofc.sendMessage(from, {
        react: { text: "✅", key: mek.key },
      });

    } catch (e) {
      console.log(e);
      reply("❌ *An error occurred while searching!*");
    }
  }
);

// ============================================
// SINHALACARTOONS INFO
// ============================================

cmd(
  {
    pattern: "scinfo",
    react: "📋",
    dontAddCommandList: true,
    filename: __filename,
  },
  async (manaofc, mek, m, { from, prefix, q, reply, config }) => {
    try {
      if (!q) return reply("❌ *Need a cartoon link!*");

      await manaofc.sendMessage(from, {
        react: { text: "⏳", key: mek.key },
      });

      const api = await fetch("https://manaofc-api.vercel.app/sinhalacartoons/info?url=" + encodeURIComponent(q));
      const res = await api.json();

      if (!res.title) {
        return reply("❌ *Failed to get cartoon info!*");
      }

      const data = res;
      const desc = data.content ? (data.content.length > 300 ? data.content.slice(0, 300) + "..." : data.content) : "No description available.";
      
      const caption = `*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n*📺 ${data.title}*\n\n` +
                `*📅 Date:* ${data.date ? new Date(data.date).toLocaleDateString() : "N/A"}\n` +
                `*👤 Author:* ${data.author || "N/A"}\n` +
                `*📂 Category:* ${data.category || "N/A"}\n` +
                `*╰━━━━━━━✧༺♥༻✧━━━━━━━*`;
      
      const buttons = [{
        buttonId: prefix + "scdown " + encodeURIComponent(data.url),
        buttonText: { displayText: "📥 Get Download" },
        type: 1
      }];

      const buttonMessage = {
        image: data.featuredImage,
        caption: caption,
        footer: config.FOOTER || config.FOOTER,
        buttons: buttons,
        headerType: 4
      };

      await manaofc.buttonMessage(from, buttonMessage, mek);

      await manaofc.sendMessage(from, {
        react: { text: "✅", key: mek.key },
      });

    } catch (e) {
      console.log(e);
      reply("❌ *Failed to get cartoon info!*");
    }
  }
);

// ============================================
// SINHALACARTOONS DOWNLOAD (List Episodes)
// ============================================

cmd(
  {
    pattern: "scdown",
    react: "📁",
    dontAddCommandList: true,
    filename: __filename,
  },
  async (manaofc, mek, m, { from, prefix, q, reply, config }) => {
    try {
      if (!q) return reply("❌ *Need a cartoon URL!*");

      await manaofc.sendMessage(from, {
        react: { text: "⬇️", key: mek.key },
      });

      const postUrl = decodeURIComponent(q);
      const api = await fetch("https://manaofc-api.vercel.app/sinhalacartoons/download?url=" + encodeURIComponent(postUrl));
      const res = await api.json();

      if (!res.downloadLinks || res.downloadLinks.length === 0) {
        return reply("❌ *Failed to get download links!*");
      }

      // Get only direct links, ignore telegram
      const directLinkObj = res.downloadLinks.find(dl => dl.type === "direct");
      
      if (!directLinkObj || !directLinkObj.directUrls || directLinkObj.directUrls.length === 0) {
        return reply("❌ *No direct download links found!*");
      }

      const episodes = directLinkObj.directUrls;
      
      // Build list rows (each episode = one row)
      const rows = episodes.map((url, index) => {
        const fileName = url.split('/').pop() || `Episode ${index + 1}`;
        return {
          title: `📀 ${fileName}`,
          description: `Click to download ${fileName}`,
          rowId: prefix + "scget " + index + " " + encodeURIComponent(postUrl)
        };
      });

      const sections = [{
        title: "Available Episodes",
        rows: rows
      }];

      const listMessage = {
        text: `*📥 ${res.title}*\n\n*Total Episodes:* ${episodes.length}\n\nSelect the list below to download:`,
        footer: config.FOOTER || config.FOOTER,
        title: res.title.length > 50 ? res.title.slice(0, 47) + "..." : res.title,
        buttonText: "📂 View Episodes",
        sections: sections
      };

      await manaofc.listMessage(from, listMessage, mek);

      await manaofc.sendMessage(from, {
        react: { text: "✅", key: mek.key },
      });

    } catch (e) {
      console.log(e);
      reply("❌ *Failed to get download links!*");
    }
  }
);

// ============================================
// SINHALACARTOONS GET FILE (Send Episode)
// ============================================

cmd(
  {
    pattern: "scget",
    react: "📤",
    dontAddCommandList: true,
    filename: __filename,
  },
  async (manaofc, mek, m, { from, q, reply }) => {
    try {
      if (!q) return reply("❌ *Need download parameters!*");
      
      const parts = q.split(" ");
      const index = parseInt(parts[0]);
      const postUrl = decodeURIComponent(parts.slice(1).join(" "));
      
      if (isNaN(index) || !postUrl) return reply("❌ *Invalid download parameters!*");

      await manaofc.sendMessage(from, {
        react: { text: "⬆️", key: mek.key },
      });

      const api = await fetch("https://manaofc-api.vercel.app/sinhalacartoons/download?url=" + encodeURIComponent(postUrl));
      const res = await api.json();

      if (!res.downloadLinks) {
        return reply("❌ *Failed to fetch download links!*");
      }

      const directLinkObj = res.downloadLinks.find(dl => dl.type === "direct");
      
      if (!directLinkObj || !directLinkObj.directUrls || !directLinkObj.directUrls[index]) {
        return reply("❌ *Episode not found!*");
      }

      const downloadUrl = directLinkObj.directUrls[index];
      const fileName = downloadUrl.split('/').pop() || "episode.mp4";

      await manaofc.sendMessage(
        from,
        {
          document: { url: downloadUrl },
          mimetype: "video/mp4",
          fileName: fileName,
        },
        { quoted: mek }
      );

      await manaofc.sendMessage(from, {
        react: { text: "✅", key: mek.key },
      });

    } catch (e) {
      console.log(e);
      reply("❌ *Download failed!*");
    }
  }
);

// ============================================
// ZOOM SEARCH COMMAND
// ============================================
cmd({
    pattern: "zoom",
    desc: "Search Sinhala subtitles from Zoom.lk",
    use: ".zoom <movie name>",
    react: "📝",
    category: "movie",
    filename: __filename
},
async (manaofc, mek, m, { from, prefix, q, reply, config }) => {
    try {
        if (!q) return reply("*🔍 Please enter a movie name!*\n\nExample: `.zoom avatar`");

        const response = await fetch(
            "https://manaofc-api.vercel.app/zoom/search?q=" + encodeURIComponent(q)
        );

        const res = await response.json();

        if (!res.results || res.results.length < 1) {
            return reply("*❌ No results found!*");
        }

        const rows = res.results.slice(0, 10).map((v) => ({
            buttonId: prefix + "dzoom " + v.link,
            buttonText: {
                displayText: v.title.length > 40 ? v.title.slice(0, 37) + "..." : v.title
            },
            type: 1
        }));

        const buttonMessage = {
            image: "https://files.catbox.moe/higob5.png",
            caption: `*📝 ${config.BOT_NAME || config.BOT_NAME} ZOOM*`,
            footer: config.FOOTER || config.FOOTER,
            buttons: rows,
            headerType: 4
        };

       await manaofc.buttonMessage(from, buttonMessage, mek);

    } catch (e) {
        console.log(e);
        reply("*❌ Error occurred while searching!*");
    }
});

// ============================================
// ZOOM DOWNLOAD COMMAND (AUTO DOCUMENT SEND)
// ============================================
cmd({
    pattern: "dzoom",
    desc: "Download Sinhala subtitle from Zoom.lk",
    react: "⬇️",
    dontAddCommandList: true,
    filename: __filename
},
async (manaofc, mek, m, { from, q, reply, config }) => {
    try {
        if (!q) return reply("*Need a post URL!*");

        const response = await fetch(
            "https://manaofc-api.vercel.app/zoom/post?url=" + encodeURIComponent(q)
        );

        const res = await response.json();

        if (!res.title || !res.downloadLink) {
            return reply("*❌ Failed to get subtitle info!*");
        }

        const cleanTitle = res.title.replace(/[^a-zA-Z0-9\s]/g, "").replace(/\s+/g, "_");
        const fileName = cleanTitle + ".srt";

        const infoCaption = "*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n*📝 Subtitle Info*\n\n" +
                           "*Title:* " + res.title + "\n" +
                           "*Author:* " + (res.author || "N/A") + "\n" +
                           "*Views:* " + (res.view || "N/A") + "\n" +
                           "*Hits:* " + (res.downloadHits || "N/A") + "\n" +
                           "*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n" +
                           "*⬇️ Downloading subtitle...*";

        await manaofc.sendMessage(from, { text: infoCaption }, { quoted: mek });

        try {
            await manaofc.sendMessage(from, {
                document: { url: res.downloadLink },
                mimetype: "application/x-subrip",
                fileName: fileName,
                caption: "*✅ " + res.title + "*\n*📥 " + (res.downloadHits || "") + "*"
            }, { quoted: mek });

        } catch (downloadError) {
            console.log("Download failed:", downloadError);

            await manaofc.sendMessage(from, {
                text: "*❌ Direct download failed!*\n\n" +
                      "*Title:* " + res.title + "\n" +
                      "*Download Link:* " + res.downloadLink + "\n\n" +
                      "Please download manually."
            }, { quoted: mek });
        }

    } catch (e) {
        console.log(e);
        reply("*❌ Error occurred!*");
    }
});



//=====================================
// ========== OWNER COMMANDS ==========
//=====================================

// 3. BROADCAST MESSAGE
cmd({
    pattern: "broadcast",
    react: "📢",
    alias: ["bc", "cast"],
    desc: "Broadcast message to all chats",
    category: "owner",
    use: ".broadcast <message>",
    filename: __filename
},
async (manaofc, mek, m, { from, isOwner, reply, q, config }) => {
    try {
        if (!isOwner) return reply("❌ *Only owner can use this!*");
        if (!q) return reply("❌ *Provide a message to broadcast!*");

        const chats = await manaofc.groupFetchAllParticipating();
        const groups = Object.values(chats);

        let count = 0;
        for (let group of groups) {
            await manaofc.sendMessage(group.id, { text: `*📢 BROADCAST*

${q}` });
            count++;
            await delay(500);
        }

        reply(`✅ *Broadcast sent to ${count} groups!*`);

    } catch (e) {
        console.error(e);
        reply("❌ *Broadcast failed!*");
    }
});

// 4. LEAVE GROUP
cmd({
    pattern: "leave",
    react: "👋",
    desc: "Leave current group",
    category: "owner",
    use: ".leave",
    filename: __filename
},
async (manaofc, mek, m, { from, isGroup, isOwner, reply, config }) => {
    try {
        if (!isOwner) return reply("❌ *Only owner can use this!*");
        if (!isGroup) return reply("❌ *This is not a group!*");

        await reply("👋 *Leaving group...*");
        await delay(1000);
        await manaofc.groupLeave(from);

    } catch (e) {
        console.error(e);
        reply("❌ *Error!*");
    }
});

// 5. BLOCK USER
cmd({
    pattern: "block",
    react: "🚫",
    desc: "Block a user",
    category: "owner",
    use: ".block @user or reply",
    filename: __filename
},
async (manaofc, mek, m, { from, isOwner, reply, config }) => {
    try {
        if (!isOwner) return reply("❌ *Only owner can use this!*");

        let users = mek.mentionedJid ? mek.mentionedJid[0] : (mek.quoted ? mek.quoted.sender : null);
        if (!users) return reply("❌ *Mention or reply to a user!*");

        await manaofc.updateBlockStatus(users, "block");
        reply(`🚫 *Blocked @${users.split('@')[0]}*`);

    } catch (e) {
        console.error(e);
        reply("❌ *Failed to block user!*");
    }
});

// 6. UNBLOCK USER
cmd({
    pattern: "unblock",
    react: "✅",
    desc: "Unblock a user",
    category: "owner",
    use: ".unblock @user or reply",
    filename: __filename
},
async (manaofc, mek, m, { from, isOwner, reply, config }) => {
    try {
        if (!isOwner) return reply("❌ *Only owner can use this!*");

        let users = mek.mentionedJid ? mek.mentionedJid[0] : (mek.quoted ? mek.quoted.sender : null);
        if (!users) return reply("❌ *Mention or reply to a user!*");

        await manaofc.updateBlockStatus(users, "unblock");
        reply(`✅ *Unblocked @${users.split('@')[0]}*`);

    } catch (e) {
        console.error(e);
        reply("❌ *Failed to unblock user!*");
    }
});

// 7. SET BOT BIO/ABOUT
cmd({
    pattern: "setbio",
    react: "📝",
    desc: "Set bot status/bio",
    category: "owner",
    use: ".setbio <text>",
    filename: __filename
},
async (manaofc, mek, m, { from, isOwner, reply, q, config }) => {
    try {
        if (!isOwner) return reply("❌ *Only owner can use this!*");
        if (!q) return reply("❌ *Provide a bio text!*");

        await manaofc.updateProfileStatus(q);
        reply(`✅ *Bio updated to:* ${q}`);

    } catch (e) {
        console.error(e);
        reply("❌ *Failed to update bio!*");
    }
});

// 8. SET BOT NAME
cmd({
    pattern: "setname",
    react: "✏️",
    desc: "Set bot profile name",
    category: "owner",
    use: ".setname <name>",
    filename: __filename
},
async (manaofc, mek, m, { from, isOwner, reply, q, config }) => {
    try {
        if (!isOwner) return reply("❌ *Only owner can use this!*");
        if (!q) return reply("❌ *Provide a name!*");

        await manaofc.updateProfileName(q);
        reply(`✅ *Profile name updated to:* ${q}`);

    } catch (e) {
        console.error(e);
        reply("❌ *Failed to update name!*");
    }
});



//===================================
//====== AI COMMAND =================
//===================================

// ========== GROQ AI ==========
cmd({
    pattern: "groq",
    react: '🤖',
    alias: ["groqai"],
    desc: "Chat with Groq AI",
    category: "ai",
    use: '.groq <question>',
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply, config }) => {
    try {
        if (!q) return await reply("❓ *Please ask me something!*\n\nExample: `.groq hi`");
        
        await manaofc.sendMessage(from, { react: { text: "⏳", key: mek.key } });
        
        const res = await fetch('https://manaofc-api.vercel.app/ai/groq?q=' + encodeURIComponent(q));
        const result = await res.json();
        
        if (!result.success || !result.message) {
            return await reply("❌ *Failed to get response from Groq AI.*");
        }
        
        const text = `🤖 *Groq AI* (${result.model})\n\n${result.message}\n\n${config.FOOTER || ''}`;
        
        await manaofc.sendMessage(from, { text }, { quoted: mek });
        await manaofc.sendMessage(from, { react: { text: "✅", key: mek.key } });
        
    } catch (e) {
        await reply("❌ *Error:* " + e.message);
        console.log(e);
    }
});

// ========== SAMBANOVA AI ==========
cmd({
    pattern: "sambanova",
    react: '⚡',
    alias: ["samba", "snova"],
    desc: "Chat with Sambanova AI",
    category: "ai",
    use: '.sambanova <question>',
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply, config }) => {
    try {
        if (!q) return await reply("❓ *Please ask me something!*\n\nExample: `.sambanova hi`");
        
        await manaofc.sendMessage(from, { react: { text: "⏳", key: mek.key } });
        
        const res = await fetch('https://manaofc-api.vercel.app/ai/sambanova?q=' + encodeURIComponent(q));
        const result = await res.json();
        
        if (!result.success || !result.message) {
            return await reply("❌ *Failed to get response from Sambanova AI.*");
        }
        
        const text = `⚡ *Sambanova AI* (${result.model})\n\n${result.message}\n\n${config.FOOTER || ''}`;
        
        await manaofc.sendMessage(from, { text }, { quoted: mek });
        await manaofc.sendMessage(from, { react: { text: "✅", key: mek.key } });
        
    } catch (e) {
        await reply("❌ *Error:* " + e.message);
        console.log(e);
    }
});

// ========== MISTRAL AI ==========
cmd({
    pattern: "mistral",
    react: '🌊',
    alias: ["mistralai"],
    desc: "Chat with Mistral AI",
    category: "ai",
    use: '.mistral <question>',
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply, config }) => {
    try {
        if (!q) return await reply("❓ *Please ask me something!*\n\nExample: `.mistral hi`");
        
        await manaofc.sendMessage(from, { react: { text: "⏳", key: mek.key } });
        
        const res = await fetch('https://manaofc-api.vercel.app/ai/mistral?q=' + encodeURIComponent(q));
        const result = await res.json();
        
        if (!result.success || !result.message) {
            return await reply("❌ *Failed to get response from Mistral AI.*");
        }
        
        const text = `🌊 *Mistral AI* (${result.model})\n\n${result.message}\n\n${config.FOOTER || ''}`;
        
        await manaofc.sendMessage(from, { text }, { quoted: mek });
        await manaofc.sendMessage(from, { react: { text: "✅", key: mek.key } });
        
    } catch (e) {
        await reply("❌ *Error:* " + e.message);
        console.log(e);
    }
});


//=====================================
// ========== SEARCH COMMAND ==========
//=====================================
const isUrl = (url) => {
    return url.match(
        new RegExp(
            /https?:\/\/(www\.)?[-a-zA-Z0-9@:%.+~#=]{1,256}\.[a-zA-Z0-9()]{1,6}\b([-a-zA-Z0-9()@:%+.~#?&/=]*)/,
            'gi'
        )
    )
}

function ytreg(url) {
    const ytIdRegex = /(?:http(?:s|):\/\/|)(?:(?:www\.|)youtube(?:\-nocookie|)\.com\/(?:watch\?.*(?:|\&)v=|embed|shorts\/|v\/)|youtu\.be\/)([-_0-9A-Za-z]{11})/
    return ytIdRegex.test(url);
}

cmd({
    pattern: "yts",
    alias: ["y"],
    use: '.yts lelena',
    react: "🔎",
    desc: "Search Youtube Songs or Videos.",
    category: "search",
    filename: __filename
},
async(manaofc, mek, m, {from, q, reply, config}) => {
    try {
        if (!q) return await reply("❌ *Please provide a search query!*\n\n*Example:* `.yts lelena`")
        if(isUrl(q) && !ytreg(q)) return await reply("❌ *Invalid YouTube URL!*")
        
        await manaofc.sendMessage(from, { react: { text: "🔍", key: mek.key } });
        
        const arama = await yts(q);
        
        if (!arama || !arama.all || arama.all.length === 0) {
            return await reply("❌ *No results found!*")
        }
        
        let mesaj = `*🔎 ${config.BOT_NAME || config.BOT_NAME} YOUTUBE SEARCH*\n\n`;
        
        arama.all.slice(0, 10).forEach((video) => {
            mesaj += `*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n`;
            mesaj += `*╎◈ Title :* ${video.title}\n`;
            mesaj += `*╎🔗 Link :* ${video.url}\n`;
            mesaj += `*╎⏱️ Duration :* ${video.timestamp || 'N/A'}\n`;
            mesaj += `*╎👀 Views :* ${video.views || 'N/A'}\n`;
            mesaj += `*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n`;
        });
        
        mesaj += `${config.FOOTER || config.FOOTER}`;
        
        await manaofc.sendMessage(from, { text: mesaj }, { quoted: mek });
        
    } catch (e) {
        console.log(e);
        reply('*Error !!*')
    }
});


//====================================
// ========== LOGO COMMANDS ==========
//====================================
// Helper: Download image buffer from URL
async function getBuffer(url) {
    try {
        const response = await axios.get(url, { 
            responseType: 'arraybuffer',
            timeout: 30000
        });
        return Buffer.from(response.data);
    } catch (e) {
        throw new Error("Failed to download image: " + e.message);
    }
}

// Helper: Generate image using Pollinations AI (FREE - No API Key)
async function generatePollinationsImage(prompt, options = {}) {
    const {
        width = 1024,
        height = 1024,
        seed = Math.floor(Math.random() * 1000000),
        model = 'flux',
        nologo = true
    } = options;

    // Pollinations AI - Completely FREE, No API Key needed
    const encodedPrompt = encodeURIComponent(prompt);
    const url = `https://image.pollinations.ai/prompt/${encodedPrompt}?width=${width}&height=${height}&seed=${seed}&model=${model}&nologo=${nologo}`;

    return await getBuffer(url);
}
//=========================

const logoStyles = [
    { pattern: "neon", react: "💡", prompt: (text) => `Neon glowing text logo "${text}", cyberpunk style, vibrant neon colors, glowing effect, dark background, high quality, professional logo design` },
    { pattern: "glitch", react: "👾", prompt: (text) => `Glitch effect text logo "${text}", digital distortion, RGB split, cyber glitch art, retro tech style, dark background, high quality` },
    { pattern: "metal", react: "🔩", prompt: (text) => `Metallic 3D text logo "${text}", chrome metal effect, reflective surface, gold and silver, industrial style, professional logo, high quality` },
    { pattern: "firelogo", react: "🔥", prompt: (text) => `Fire and flames text logo "${text}", burning fire effect, orange and red flames, intense heat, dark background, epic style, high quality` },
    { pattern: "graffiti", react: "🎨", prompt: (text) => `Graffiti street art text logo "${text}", colorful spray paint, urban wall art style, hip hop culture, vibrant colors, brick wall background, high quality` },
    { pattern: "logo3d", react: "🧊", prompt: (text) => `3D extruded text logo "${text}", three dimensional depth, shadows and lighting, modern geometric style, clean background, professional logo, high quality render` },
    { pattern: "gaming", react: "🎮", prompt: (text) => `Gaming esports text logo "${text}", aggressive font style, red and black colors, battle royale theme, professional gaming team logo, high quality` },
    { pattern: "devil", react: "😈", prompt: (text) => `Devil demon text logo "${text}", horns and fire, dark evil style, red and black colors, hell theme, scary font, high quality` },
    { pattern: "wolf", react: "🐺", prompt: (text) => `Wolf howling text logo "${text}", wolf silhouette, moon and stars, galaxy background, blue and silver colors, wild nature theme, high quality` },
    { pattern: "joker", react: "🃏", prompt: (text) => `Joker clown text logo "${text}", playing cards, purple and green colors, chaotic madness style, dark gothic theme, high quality` },
    { pattern: "blackpink", react: "💗", prompt: (text) => `Kpop pink neon text logo "${text}", Blackpink style, pink and black colors, girly aesthetic, sparkles and hearts, high quality` },
    { pattern: "cloud", react: "☁️", prompt: (text) => `Cloud sky text logo "${text}", fluffy white clouds, blue sky background, heavenly dreamy style, soft colors, peaceful, high quality` },
    { pattern: "thunder", react: "⚡", prompt: (text) => `Thunder lightning text logo "${text}", electric blue lightning bolts, stormy dark clouds, powerful energy, electric sparks, high quality` },
    { pattern: "blood", react: "🩸", prompt: (text) => `Blood dripping text logo "${text}", horror style, red blood splatter, dark creepy background, scary font, Halloween theme, high quality` },
    { pattern: "sand", react: "🏖️", prompt: (text) => `Sand beach text "${text}", written in wet sand, tropical beach, ocean waves, sunset background, realistic, high quality` },
    { pattern: "coffee", react: "☕", prompt: (text) => `Coffee cup text logo "${text}", latte art style, coffee beans, warm brown colors, cozy cafe aesthetic, steam rising, high quality` },
    { pattern: "christmas", react: "🎄", prompt: (text) => `Christmas holiday text logo "${text}", snowflakes, Christmas tree, red and green colors, festive decorations, winter theme, high quality` },
    { pattern: "love", react: "❤️", prompt: (text) => `Love romantic text logo "${text}", red hearts, roses, pink and red colors, valentine theme, cute aesthetic, high quality` },
    { pattern: "wood", react: "🪵", prompt: (text) => `Wood carved text logo "${text}", engraved in wooden planks, rustic natural style, brown wood texture, forest theme, high quality` },
    { pattern: "galaxy", react: "🌌", prompt: (text) => `Galaxy space text logo "${text}", stars and nebula, purple and blue cosmic colors, universe theme, glowing stars, high quality` },
    { pattern: "retro", react: "📺", prompt: (text) => `Retro vintage text logo "${text}", 80s style, VHS effect, old TV static, neon grid, synthwave colors, nostalgic, high quality` },
    { pattern: "watercolor", react: "🎨", prompt: (text) => `Watercolor paint text logo "${text}", artistic brush strokes, colorful splashes, hand painted style, soft pastel colors, creative art, high quality` },
    { pattern: "gold", react: "🏆", prompt: (text) => `Gold luxury text logo "${text}", golden shiny letters, rich elegant style, diamonds and jewels, black background, premium feel, high quality` },
    { pattern: "ice", react: "🧊", prompt: (text) => `Ice frozen text logo "${text}", crystal ice effect, snowflakes, winter cold theme, blue and white colors, frosty, high quality` },
    { pattern: "ninja", react: "🥷", prompt: (text) => `Ninja warrior text logo "${text}", Japanese katana, shadow silhouette, black and red colors, martial arts theme, stealth, high quality` },
    { pattern: "dragon", react: "🐉", prompt: (text) => `Dragon fire text logo "${text}", mythical dragon, scales and fire, epic fantasy style, gold and red colors, powerful, high quality` },
    { pattern: "anime", react: "🇯🇵", prompt: (text) => `Anime manga text logo "${text}", Japanese anime style, colorful kawaii, cherry blossoms, cute characters, vibrant colors, high quality` },
    { pattern: "skull", react: "💀", prompt: (text) => `Skull skeleton text logo "${text}", skull and crossbones, dark gothic style, bones and graveyard, horror punk theme, high quality` },
];

logoStyles.forEach(style => {
    cmd({
        pattern: style.pattern,
        react: style.react,
        desc: `Create ${style.pattern} style text logo`,
        category: "logo",
        use: `.${style.pattern} <text>`,
        filename: __filename
    },
    async (manaofc, mek, m, { from, q, reply, config }) => {
        try {
            if (!q) return reply(`❌ *Provide text!*\nExample: \`.${style.pattern} MANAOFC\``);

            await manaofc.sendMessage(from, { react: { text: "⏳", key: mek.key } });

            const prompt = style.prompt(q);
            const buffer = await generatePollinationsImage(prompt, { width: 1024, height: 512 });

            await manaofc.sendMessage(from, {
                image: buffer,
                caption: `${style.react} *${style.pattern.charAt(0).toUpperCase() + style.pattern.slice(1)} Logo*\n\nText: ${q}\n${config.FOOTER || '> _*Powered By Manaofc*_'} `
            }, { quoted: mek });

        } catch (e) {
            console.error(e);
            reply(`❌ *Failed to create ${style.pattern} logo!*\n` + e.message);
        }
    });
});

// ============================================
// ============================================
// ========== CONVERT COMMANDS ==========
// ============================================

// 1. IMAGE TO STICKER
cmd({
    pattern: "sticker",
    react: "🎨",
    alias: ["s", "stic"],
    desc: "Convert image/video/gif to sticker",
    category: "convert",
    use: ".sticker (reply to image/video)",
    filename: __filename
},
async (manaofc, mek, m, { from, reply, config }) => {
    try {
        const quoted = mek.message?.extendedTextMessage?.contextInfo?.quotedMessage;
        if (!quoted) return reply("❌ *Reply to an image, video, or GIF!*");
        const msgType = getContentType(quoted);
        if (!msgType || (!msgType.includes('image') && !msgType.includes('video'))) {
            return reply("❌ *Reply to an image or video!*");
        }
        await manaofc.sendMessage(from, { react: { text: "🎨", key: mek.key } });
        const mediaMsg = quoted[msgType];
        const stream = await downloadContentFromMessage(mediaMsg, msgType.replace('Message', ''));
        let chunks = [];
        for await (const chunk of stream) chunks.push(chunk);
        const buffer = Buffer.concat(chunks);
        await manaofc.sendMessage(from, {
            sticker: buffer,
            packname: config.BOT_NAME || 'MANAOFC LITE',
            author: 'Manaofc'
        }, { quoted: mek });
    } catch (e) {
        console.error(e);
        reply("❌ *Failed to create sticker!*");
    }
});

// 2. STICKER TO IMAGE
cmd({
    pattern: "toimg",
    react: "🖼️",
    alias: ["stickertoimage", "img"],
    desc: "Convert sticker to image",
    category: "convert",
    use: ".toimg (reply to sticker)",
    filename: __filename
},
async (manaofc, mek, m, { from, reply, config }) => {
    try {
        const quoted = mek.message?.extendedTextMessage?.contextInfo?.quotedMessage;
        if (!quoted) return reply("❌ *Reply to a sticker!*");
        const msgType = getContentType(quoted);
        if (!msgType || !msgType.includes('sticker')) {
            return reply("❌ *Reply to a sticker!*");
        }
        await manaofc.sendMessage(from, { react: { text: "🖼️", key: mek.key } });
        const mediaMsg = quoted[msgType];
        const stream = await downloadContentFromMessage(mediaMsg, 'image');
        let chunks = [];
        for await (const chunk of stream) chunks.push(chunk);
        const buffer = Buffer.concat(chunks);
        await manaofc.sendMessage(from, {
            image: buffer,
            caption: `> _*Powered By Manaofc*_ ⚡

🖼️ *Sticker converted to image*`
        }, { quoted: mek });
    } catch (e) {
        console.error(e);
        reply("❌ *Failed to convert sticker!*");
    }
});

// 3. VIDEO TO AUDIO (MP3)
cmd({
    pattern: "tomp3",
    react: "🎵",
    alias: ["toaudio", "mp3"],
    desc: "Convert video to audio/mp3",
    category: "convert",
    use: ".tomp3 (reply to video)",
    filename: __filename
},
async (manaofc, mek, m, { from, reply, config }) => {
    try {
        const quoted = mek.message?.extendedTextMessage?.contextInfo?.quotedMessage;
        if (!quoted) return reply("❌ *Reply to a video!*");
        const msgType = getContentType(quoted);
        if (!msgType || !msgType.includes('video')) {
            return reply("❌ *Reply to a video!*");
        }
        await manaofc.sendMessage(from, { react: { text: "🎵", key: mek.key } });
        const mediaMsg = quoted[msgType];
        const stream = await downloadContentFromMessage(mediaMsg, 'video');
        let chunks = [];
        for await (const chunk of stream) chunks.push(chunk);
        const buffer = Buffer.concat(chunks);
        await manaofc.sendMessage(from, {
            audio: buffer,
            mimetype: "audio/mpeg",
            ptt: false
        }, { quoted: mek });
        await manaofc.sendMessage(from, { react: { text: "✅", key: mek.key } });
    } catch (e) {
        console.error(e);
        reply("❌ *Failed to convert to audio!*");
    }
});

// 4. VIDEO TO DOCUMENT
cmd({
    pattern: "todoc",
    react: "📁",
    alias: ["todocument", "doc"],
    desc: "Convert media to document",
    category: "convert",
    use: ".todoc (reply to image/video)",
    filename: __filename
},
async (manaofc, mek, m, { from, reply, config }) => {
    try {
        const quoted = mek.message?.extendedTextMessage?.contextInfo?.quotedMessage;
        if (!quoted) return reply("❌ *Reply to an image or video!*");
        const msgType = getContentType(quoted);
        if (!msgType || (!msgType.includes('image') && !msgType.includes('video'))) {
            return reply("❌ *Reply to an image or video!*");
        }
        await manaofc.sendMessage(from, { react: { text: "📁", key: mek.key } });
        const mediaMsg = quoted[msgType];
        const mediaType = msgType.replace('Message', '');
        const stream = await downloadContentFromMessage(mediaMsg, mediaType);
        let chunks = [];
        for await (const chunk of stream) chunks.push(chunk);
        const buffer = Buffer.concat(chunks);
        const ext = msgType.includes('image') ? 'jpg' : 'mp4';
        const mimetype = msgType.includes('image') ? 'image/jpeg' : 'video/mp4';
        await manaofc.sendMessage(from, {
            document: buffer,
            mimetype: mimetype,
            fileName: `converted_${Date.now()}.${ext}`,
            caption: `> _*Powered By Manaofc*_ ⚡

📁 *Converted to Document*`
        }, { quoted: mek });
    } catch (e) {
        console.error(e);
        reply("❌ *Failed to convert to document!*");
    }
});

// 5. IMAGE TO URL (UPLOAD)
cmd({
    pattern: "tourl",
    react: "🔗",
    alias: ["upload", "imgurl"],
    desc: "Upload image/video to get URL",
    category: "convert",
    use: ".tourl (reply to image/video)",
    filename: __filename
},
async (manaofc, mek, m, { from, reply, config }) => {
    try {
        const quoted = mek.message?.extendedTextMessage?.contextInfo?.quotedMessage;
        if (!quoted) return reply("❌ *Reply to an image or video!*");
        const msgType = getContentType(quoted);
        if (!msgType || (!msgType.includes('image') && !msgType.includes('video'))) {
            return reply("❌ *Reply to an image or video!*");
        }
        await manaofc.sendMessage(from, { react: { text: "⬆️", key: mek.key } });
        const mediaMsg = quoted[msgType];
        const mediaType = msgType.replace('Message', '');
        const stream = await downloadContentFromMessage(mediaMsg, mediaType);
        let chunks = [];
        for await (const chunk of stream) chunks.push(chunk);
        const buffer = Buffer.concat(chunks);
        const boundary = '----WebKitFormBoundary' + Math.random().toString(36).substring(2);
        const data = Buffer.concat([
            Buffer.from(`--${boundary}
Content-Disposition: form-data; name="file"; filename="file.jpg"
Content-Type: image/jpeg

`),
            buffer,
            Buffer.from(`
--${boundary}--
`)
        ]);
        const uploadRes = await axios.post('https://0x0.st', data, {
            headers: { 'Content-Type': `multipart/form-data; boundary=${boundary}` }
        });
        const url = uploadRes.data.trim();
        await manaofc.sendMessage(from, {
            text: `> _*Powered By Manaofc*_ ⚡

*╭━━━━━━━✧༺♥༻✧━━━━━━━*
🔗 *Upload Complete*

📥 *URL:* ${url}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*`
        }, { quoted: mek });
    } catch (e) {
        console.error(e);
        reply("❌ *Upload failed!*\n\nTry again later.");
    }
});

// 6. REVERSE VIDEO
cmd({
    pattern: "reverse",
    react: "🔄",
    desc: "Reverse a video (reply to video)",
    category: "convert",
    use: ".reverse (reply to video)",
    filename: __filename
},
async (manaofc, mek, m, { from, reply, config }) => {
    try {
        const quoted = mek.message?.extendedTextMessage?.contextInfo?.quotedMessage;
        if (!quoted) return reply("❌ *Reply to a video!*");
        const msgType = getContentType(quoted);
        if (!msgType || !msgType.includes('video')) {
            return reply("❌ *Reply to a video!*");
        }
        await manaofc.sendMessage(from, { react: { text: "🔄", key: mek.key } });
        const mediaMsg = quoted[msgType];
        const stream = await downloadContentFromMessage(mediaMsg, 'video');
        let chunks = [];
        for await (const chunk of stream) chunks.push(chunk);
        const buffer = Buffer.concat(chunks);
        const tmpFile = path.join(os.tmpdir(), `tmp_${Date.now()}.mp4`);
        const outFile = path.join(os.tmpdir(), `rev_${Date.now()}.mp4`);
        fs.writeFileSync(tmpFile, buffer);
        await execAsync(`ffmpeg -i "${tmpFile}" -vf reverse -af areverse "${outFile}"`);
        const reversedBuffer = fs.readFileSync(outFile);
        await manaofc.sendMessage(from, {
            video: reversedBuffer,
            caption: `> _*Powered By Manaofc*_ ⚡

🔄 *Video Reversed*`
        }, { quoted: mek });
        fs.unlinkSync(tmpFile);
        fs.unlinkSync(outFile);
    } catch (e) {
        console.error(e);
        reply("❌ *Reverse failed!*\nMake sure ffmpeg is installed.");
    }
});

// ============================================
// ========== TOOLS COMMANDS ==========
// ============================================

// 1. CALCULATOR
cmd({
    pattern: "calc",
    react: "🧮",
    alias: ["calculate", "math"],
    desc: "Calculate math expressions",
    category: "tools",
    use: ".calc <expression>",
    filename: __filename
},
async (manaofc, mek, m, { from, q, reply, config }) => {
    try {
        if (!q) return reply("❌ *Provide a math expression!*\n\nExample: `.calc 5 + 5 * 2`");
        const expression = q.replace(/[^0-9+\-*/().\s%^]/g, '');
        if (!expression) return reply("❌ *Invalid expression!*");
        const result = Function('"use strict"; return (' + expression + ')')();
        const text = `> _*Powered By Manaofc*_ ⚡

*╭━━━━━━━✧༺♥༻✧━━━━━━━*
🧮 *Calculator*

📥 *Expression:* ${expression}
📤 *Result:* ${result}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*`;
        await manaofc.sendMessage(from, { text }, { quoted: mek });
    } catch (e) {
        reply("❌ *Invalid math expression!*");
    }
});

// 2. QR CODE GENERATOR
cmd({
    pattern: "qr",
    react: "🔲",
    desc: "Generate QR code from text",
    category: "tools",
    use: ".qr <text>",
    filename: __filename
},
async (manaofc, mek, m, { from, q, reply, config }) => {
    try {
        if (!q) return reply("❌ *Provide text to convert!*\n\nExample: `.qr https://google.com`");
        const qrUrl = `https://api.qrserver.com/v1/create-qr-code/?size=300x300&data=${encodeURIComponent(q)}`;
        await manaofc.sendMessage(from, {
            image: { url: qrUrl },
            caption: `> _*Powered By Manaofc*_ ⚡

*╭━━━━━━━✧༺♥༻✧━━━━━━━*
🔲 *QR Code Generated*

📝 *Text:* ${q}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*`
        }, { quoted: mek });
    } catch (e) {
        reply("❌ *Failed to generate QR code!*");
    }
});

// 3. URL SHORTENER
cmd({
    pattern: "shorturl",
    react: "🔗",
    alias: ["short", "tinyurl"],
    desc: "Shorten a long URL",
    category: "tools",
    use: ".shorturl <url>",
    filename: __filename
},
async (manaofc, mek, m, { from, q, reply, config }) => {
    try {
        if (!q || !isUrl(q)) return reply("❌ *Provide a valid URL!*\n\nExample: `.shorturl https://google.com`");
        const res = await fetch(`https://is.gd/create.php?format=simple&url=${encodeURIComponent(q)}`);
        const shortUrl = await res.text();
        if (shortUrl.startsWith("http")) {
            await manaofc.sendMessage(from, {
                text: `> _*Powered By Manaofc*_ ⚡

*╭━━━━━━━✧༺♥༻✧━━━━━━━*
🔗 *URL Shortener*

📥 *Original:* ${q}
📤 *Shortened:* ${shortUrl}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*`
            }, { quoted: mek });
        } else {
            reply("❌ *Failed to shorten URL!*");
        }
    } catch (e) {
        reply("❌ *URL shortening failed!*");
    }
});

// 4. BASE64 ENCODE/DECODE
cmd({
    pattern: "base64",
    react: "🔐",
    desc: "Encode or decode base64 text",
    category: "tools",
    use: ".base64 encode <text> / .base64 decode <text>",
    filename: __filename
},
async (manaofc, mek, m, { from, q, reply, config }) => {
    try {
        if (!q) return reply("❌ *Provide action and text!*\n\nExamples:\n`.base64 encode hello`\n`.base64 decode aGVsbG8=`");
        const args = q.trim().split(/ +/);
        const action = args[0].toLowerCase();
        const text = args.slice(1).join(" ");
        if (!text) return reply("❌ *Provide text!*");
        let result;
        if (action === "encode" || action === "en") {
            result = Buffer.from(text).toString('base64');
        } else if (action === "decode" || action === "de") {
            result = Buffer.from(text, 'base64').toString('utf8');
        } else {
            return reply("❌ *Invalid action!*\nUse: `encode` or `decode`");
        }
        await manaofc.sendMessage(from, {
            text: `> _*Powered By Manaofc*_ ⚡

*╭━━━━━━━✧༺♥༻✧━━━━━━━*
🔐 *Base64 ${action.toUpperCase()}*

📝 *Input:* ${text}
📤 *Result:* ${result}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*`
        }, { quoted: mek });
    } catch (e) {
        reply("❌ *Base64 operation failed!*\nMake sure decode text is valid base64.");
    }
});

// 5. TRANSLATE
cmd({
    pattern: "trt",
    react: "🌐",
    alias: ["translate"],
    desc: "Translate text to any language",
    category: "tools",
    use: ".trt <lang_code> <text>",
    filename: __filename
},
async (manaofc, mek, m, { from, q, reply, config }) => {
    try {
        if (!q) return reply("❌ *Provide language code and text!*\n\nExample: `.trt si Hello World`\n\n*Common codes:* si, en, ta, hi, ja, ko, fr, de, es, ru, ar, zh");
        const args = q.trim().split(/ +/);
        const lang = args[0];
        const text = args.slice(1).join(" ");
        if (!text) return reply("❌ *Provide text to translate!*");
        const res = await fetch(`https://api.mymemory.translated.net/get?q=${encodeURIComponent(text)}&langpair=en|${lang}`);
        const data = await res.json();
        if (data.responseData) {
            await manaofc.sendMessage(from, {
                text: `> _*Powered By Manaofc*_ ⚡

*╭━━━━━━━✧༺♥༻✧━━━━━━━*
🌐 *Translator*

📝 *Original:* ${text}
🔤 *Translated:* ${data.responseData.translatedText}
🎯 *Language:* ${lang.toUpperCase()}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*`
            }, { quoted: mek });
        } else {
            reply("❌ *Translation failed!*");
        }
    } catch (e) {
        reply("❌ *Translation error!*");
    }
});

// 6. PASSWORD GENERATOR
cmd({
    pattern: "password",
    react: "🔑",
    alias: ["pass", "genpass"],
    desc: "Generate a strong password",
    category: "tools",
    use: ".password <length>",
    filename: __filename
},
async (manaofc, mek, m, { from, q, reply, config }) => {
    try {
        const length = parseInt(q) || 12;
        if (length < 4 || length > 50) return reply("❌ *Length must be between 4 and 50!*");
        const chars = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789!@#$%^&*()_+";
        let password = "";
        for (let i = 0; i < length; i++) {
            password += chars.charAt(Math.floor(Math.random() * chars.length));
        }
        await manaofc.sendMessage(from, {
            text: `> _*Powered By Manaofc*_ ⚡

*╭━━━━━━━✧༺♥༻✧━━━━━━━*
🔑 *Password Generator*

🔐 *Password:* \`${password}\`
📏 *Length:* ${length}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*

⚠️ _Save this password securely!_`
        }, { quoted: mek });
    } catch (e) {
        reply("❌ *Failed to generate password!*");
    }
});

// 7. WEATHER INFO
cmd({
    pattern: "weather",
    react: "🌤️",
    alias: ["climate", "forecast"],
    desc: "Get weather information",
    category: "tools",
    use: ".weather <city>",
    filename: __filename
},
async (manaofc, mek, m, { from, q, reply, config }) => {
    try {
        if (!q) return reply("❌ *Provide a city name!*\n\nExample: `.weather Colombo`");
        const res = await fetch(`https://wttr.in/${encodeURIComponent(q)}?format=j1`);
        const data = await res.json();
        if (!data.current_condition) return reply("❌ *City not found!*");
        const current = data.current_condition[0];
        const area = data.nearest_area[0];
        const text = `> _*Powered By Manaofc*_ ⚡

*╭━━━━━━━✧༺♥༻✧━━━━━━━*
🌤️ *Weather Info*

📍 *Location:* ${area.areaName[0].value}, ${area.country[0].value}
🌡️ *Temperature:* ${current.temp_C}°C / ${current.temp_F}°F
💧 *Humidity:* ${current.humidity}%
🌬️ *Wind:* ${current.windspeedKmph} km/h
☁️ *Condition:* ${current.weatherDesc[0].value}
👁️ *Visibility:* ${current.visibility} km
*╰━━━━━━━✧༺♥༻✧━━━━━━━*`;
        await manaofc.sendMessage(from, { text }, { quoted: mek });
    } catch (e) {
        reply("❌ *Failed to fetch weather!*");
    }
});

// 8. GITHUB STALK
cmd({
    pattern: "github",
    react: "🐙",
    alias: ["gh", "git"],
    desc: "Get GitHub user information",
    category: "tools",
    use: ".github <username>",
    filename: __filename
},
async (manaofc, mek, m, { from, q, reply, config }) => {
    try {
        if (!q) return reply("❌ *Provide a GitHub username!*\n\nExample: `.github octocat`");
        const res = await fetch(`https://api.github.com/users/${encodeURIComponent(q)}`);
        if (res.status === 404) return reply("❌ *User not found!*");
        const data = await res.json();
        const text = `> _*Powered By Manaofc*_ ⚡

*╭━━━━━━━✧༺♥༻✧━━━━━━━*
🐙 *GitHub Profile*

👤 *Name:* ${data.name || data.login}
🔗 *Username:* ${data.login}
📝 *Bio:* ${data.bio || "N/A"}
📍 *Location:* ${data.location || "N/A"}
🏢 *Company:* ${data.company || "N/A"}
📊 *Public Repos:* ${data.public_repos}
👥 *Followers:* ${data.followers} | *Following:* ${data.following}
📅 *Joined:* ${new Date(data.created_at).toLocaleDateString()}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*`;
        await manaofc.sendMessage(from, {
            image: { url: data.avatar_url },
            caption: text
        }, { quoted: mek });
    } catch (e) {
        reply("❌ *Failed to fetch GitHub info!*");
    }
});

// 9. DICTIONARY
cmd({
    pattern: "define",
    react: "📖",
    alias: ["dictionary", "meaning"],
    desc: "Get word definition",
    category: "tools",
    use: ".define <word>",
    filename: __filename
},
async (manaofc, mek, m, { from, q, reply, config }) => {
    try {
        if (!q) return reply("❌ *Provide a word!*\n\nExample: `.define serendipity`");
        const res = await fetch(`https://api.dictionaryapi.dev/api/v2/entries/en/${encodeURIComponent(q)}`);
        if (res.status === 404) return reply("❌ *Word not found!*");
        const data = await res.json();
        const word = data[0];
        const meaning = word.meanings[0];
        const def = meaning.definitions[0];
        const text = `> _*Powered By Manaofc*_ ⚡

*╭━━━━━━━✧༺♥༻✧━━━━━━━*
📖 *Dictionary*

🔤 *Word:* ${word.word}
🎯 *Phonetic:* ${word.phonetic || "N/A"}
📚 *Part of Speech:* ${meaning.partOfSpeech}
📝 *Definition:* ${def.definition}
💡 *Example:* ${def.example || "N/A"}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*`;
        await manaofc.sendMessage(from, { text }, { quoted: mek });
    } catch (e) {
        reply("❌ *Failed to get definition!*");
    }
});

// 10. SCREENSHOT (WEB)
cmd({
    pattern: "ss",
    react: "📸",
    alias: ["screenshot", "webss"],
    desc: "Take website screenshot",
    category: "tools",
    use: ".ss <url>",
    filename: __filename
},
async (manaofc, mek, m, { from, q, reply, config }) => {
    try {
        if (!q || !isUrl(q)) return reply("❌ *Provide a valid URL!*\n\nExample: `.ss https://google.com`");
        const ssUrl = `https://image.thum.io/get/width/1200/crop/800/maxAge/0/${q}`;
        await manaofc.sendMessage(from, {
            image: { url: ssUrl },
            caption: `> _*Powered By Manaofc*_ ⚡

📸 *Screenshot of:* ${q}`
        }, { quoted: mek });
    } catch (e) {
        reply("❌ *Screenshot failed!*");
    }
});

// 11. BINARY ENCODE/DECODE
cmd({
    pattern: "binary",
    react: "0️⃣",
    desc: "Encode/decode binary text",
    category: "tools",
    use: ".binary encode <text> / .binary decode <binary>",
    filename: __filename
},
async (manaofc, mek, m, { from, q, reply, config }) => {
    try {
        if (!q) return reply("❌ *Provide action and text!*\n\nExamples:\n`.binary encode hello`\n`.binary decode 01101000`");
        const args = q.trim().split(/ +/);
        const action = args[0].toLowerCase();
        const text = args.slice(1).join(" ");
        if (!text) return reply("❌ *Provide text!*");
        let result;
        if (action === "encode" || action === "en") {
            result = text.split('').map(char => char.charCodeAt(0).toString(2).padStart(8, '0')).join(' ');
        } else if (action === "decode" || action === "de") {
            result = text.split(' ').map(bin => String.fromCharCode(parseInt(bin, 2))).join('');
        } else {
            return reply("❌ *Invalid action!*\nUse: `encode` or `decode`");
        }
        await manaofc.sendMessage(from, {
            text: `> _*Powered By Manaofc*_ ⚡

*╭━━━━━━━✧༺♥༻✧━━━━━━━*
0️⃣ *Binary ${action.toUpperCase()}*

📝 *Input:* ${text}
📤 *Result:* ${result}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*`
        }, { quoted: mek });
    } catch (e) {
        reply("❌ *Binary operation failed!*");
    }
});

// 12. MORSE CODE
cmd({
    pattern: "morse",
    react: "📡",
    desc: "Encode/decode morse code",
    category: "tools",
    use: ".morse encode <text> / .morse decode <morse>",
    filename: __filename
},
async (manaofc, mek, m, { from, q, reply, config }) => {
    try {
        const morseCode = {
            'A': '.-', 'B': '-...', 'C': '-.-.', 'D': '-..', 'E': '.', 'F': '..-.',
            'G': '--.', 'H': '....', 'I': '..', 'J': '.---', 'K': '-.-', 'L': '.-..',
            'M': '--', 'N': '-.', 'O': '---', 'P': '.--.', 'Q': '--.-', 'R': '.-.',
            'S': '...', 'T': '-', 'U': '..-', 'V': '...-', 'W': '.--', 'X': '-..-',
            'Y': '-.--', 'Z': '--..', '1': '.----', '2': '..---', '3': '...--',
            '4': '....-', '5': '.....', '6': '-....', '7': '--...', '8': '---..',
            '9': '----.', '0': '-----', ' ': '/'
        };
        if (!q) return reply("❌ *Provide action and text!*\n\nExamples:\n`.morse encode SOS`\n`.morse decode ... --- ...`");
        const args = q.trim().split(/ +/);
        const action = args[0].toLowerCase();
        const text = args.slice(1).join(" ").toUpperCase();
        if (!text) return reply("❌ *Provide text!*");
        let result;
        if (action === "encode" || action === "en") {
            result = text.split('').map(char => morseCode[char] || char).join(' ');
        } else if (action === "decode" || action === "de") {
            const reverseMorse = Object.fromEntries(Object.entries(morseCode).map(([k, v]) => [v, k]));
            result = text.split(' ').map(code => reverseMorse[code] || code).join('');
        } else {
            return reply("❌ *Invalid action!*\nUse: `encode` or `decode`");
        }
        await manaofc.sendMessage(from, {
            text: `> _*Powered By Manaofc*_ ⚡

*╭━━━━━━━✧༺♥༻✧━━━━━━━*
📡 *Morse ${action.toUpperCase()}*

📝 *Input:* ${text}
📤 *Result:* ${result}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*`
        }, { quoted: mek });
    } catch (e) {
        reply("❌ *Morse code operation failed!*");
    }
});

// ============================================
// ========== OTHERS COMMANDS ==========
// ============================================

// VIEW-ONCE RETRIEVER (VV)

cmd({
    pattern: "vv",
    alias: ["viewonce", "reveal"],
    desc: "Reveal view-once image or video",
    category: "others",
    react: "😎",
    filename: __filename
},
async (manaofc, mek, m, { from, reply, config }) => {
    try {
        const quoted = mek.message?.extendedTextMessage?.contextInfo?.quotedMessage;
        if (!quoted) {
            return reply("❌ *Reply to a view-once message!*");
        }

        // Handle view-once wrapper (Baileys v6+)
        const viewOnceMsg =
            quoted.viewOnceMessageV2 ||
            quoted.viewOnceMessage ||
            quoted.viewOnceMessageV2Extension ||
            null;

        const innerMsg = viewOnceMsg?.message || quoted;
        const msgType = getContentType(innerMsg);

        if (!msgType || (!msgType.includes('image') && !msgType.includes('video') && !msgType.includes('audio'))) {
            return reply("❌ *Not a view-once media message!*");
        }

        const mediaMessage = innerMsg[msgType];
        
        if (!mediaMessage?.viewOnce && !viewOnceMsg) {
            return reply("❌ *This is not a view-once message!*");
        }

        await manaofc.sendMessage(from, {
            react: { text: "👁️", key: mek.key }
        });

        // Download media
        const stream = await downloadContentFromMessage(
            mediaMessage,
            msgType.replace('Message', '')
        );

        let chunks = [];
        for await (const chunk of stream) {
            chunks.push(chunk);
        }
        const buffer = Buffer.concat(chunks);

        const caption = `> _*Powered By Manaofc*_ ⚡\n\n👁️ *View-Once Revealed*\n📂 *Type:* ${msgType.replace('Message', '').toUpperCase()}\n⏰ *Time:* ${getSriLankaTimestamp()}`;

        // Send revealed media
        if (msgType === 'imageMessage') {
            await manaofc.sendMessage(from, {
                image: buffer,
                caption: caption
            }, { quoted: mek });
        } else if (msgType === 'videoMessage') {
            await manaofc.sendMessage(from, {
                video: buffer,
                caption: caption,
                mimetype: 'video/mp4'
            }, { quoted: mek });
        } else if (msgType === 'audioMessage') {
            await manaofc.sendMessage(from, {
                audio: buffer,
                mimetype: 'audio/mp4',
                ptt: mediaMessage.ptt || false
            }, { quoted: mek });
        }

        await manaofc.sendMessage(from, {
            react: { text: "✅", key: mek.key }
        });

    } catch (err) {
        console.error("VV command error:", err);
        reply("❌ *Failed to reveal view-once media!*\n_" + err.message + "_");
    }
});
// 1. RANDOM JOKE
cmd({
    pattern: "joke",
    react: "😂",
    desc: "Get a random joke",
    category: "others",
    use: ".joke",
    filename: __filename
},
async (manaofc, mek, m, { from, reply, config }) => {
    try {
        const res = await fetch('https://official-joke-api.appspot.com/random_joke');
        const data = await res.json();
        const text = `> _*Powered By Manaofc*_ ⚡

*╭━━━━━━━✧༺♥༻✧━━━━━━━*
😂 *Random Joke*

🎭 *Setup:* ${data.setup}
🤣 *Punchline:* ${data.punchline}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*`;
        await manaofc.sendMessage(from, { text }, { quoted: mek });
    } catch (e) {
        reply("❌ *Failed to fetch joke!*");
    }
});

// 2. RANDOM QUOTE
cmd({
    pattern: "quote",
    react: "💬",
    alias: ["quotes"],
    desc: "Get an inspirational quote",
    category: "others",
    use: ".quote",
    filename: __filename
},
async (manaofc, mek, m, { from, reply, config }) => {
    try {
        const res = await fetch('https://api.quotable.io/random');
        const data = await res.json();
        const text = `> _*Powered By Manaofc*_ ⚡

*╭━━━━━━━✧༺♥༻✧━━━━━━━*
💬 *Quote of the Day*

📝 "${data.content}"

— *${data.author}*
*╰━━━━━━━✧༺♥༻✧━━━━━━━*`;
        await manaofc.sendMessage(from, { text }, { quoted: mek });
    } catch (e) {
        reply("❌ *Failed to fetch quote!*");
    }
});

// 3. RANDOM FACT
cmd({
    pattern: "fact",
    react: "🧠",
    desc: "Get a random interesting fact",
    category: "others",
    use: ".fact",
    filename: __filename
},
async (manaofc, mek, m, { from, reply, config }) => {
    try {
        const res = await fetch('https://uselessfacts.jsph.pl/random.json?language=en');
        const data = await res.json();
        const text = `> _*Powered By Manaofc*_ ⚡

*╭━━━━━━━✧༺♥༻✧━━━━━━━*
🧠 *Random Fact*

📚 ${data.text}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*`;
        await manaofc.sendMessage(from, { text }, { quoted: mek });
    } catch (e) {
        reply("❌ *Failed to fetch fact!*");
    }
});

// 4. COIN FLIP
cmd({
    pattern: "flip",
    react: "🪙",
    alias: ["coin", "coinflip"],
    desc: "Flip a coin",
    category: "others",
    use: ".flip",
    filename: __filename
},
async (manaofc, mek, m, { from, reply, config }) => {
    try {
        const result = Math.random() < 0.5 ? "Heads" : "Tails";
        const emoji = result === "Heads" ? "👤" : "🦅";
        await manaofc.sendMessage(from, {
            text: `> _*Powered By Manaofc*_ ⚡

*╭━━━━━━━✧༺♥༻✧━━━━━━━*
🪙 *Coin Flip*

${emoji} *Result:* ${result}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*`
        }, { quoted: mek });
    } catch (e) {
        reply("❌ *Error!*");
    }
});

// 5. DICE ROLL
cmd({
    pattern: "roll",
    react: "🎲",
    alias: ["dice"],
    desc: "Roll a dice",
    category: "others",
    use: ".roll",
    filename: __filename
},
async (manaofc, mek, m, { from, reply, config }) => {
    try {
        const result = Math.floor(Math.random() * 6) + 1;
        const diceEmojis = ["⚀", "⚁", "⚂", "⚃", "⚄", "⚅"];
        await manaofc.sendMessage(from, {
            text: `> _*Powered By Manaofc*_ ⚡

*╭━━━━━━━✧༺♥༻✧━━━━━━━*
🎲 *Dice Roll*

${diceEmojis[result - 1]} *Result:* ${result}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*`
        }, { quoted: mek });
    } catch (e) {
        reply("❌ *Error!*");
    }
});

// 6. RANDOM MEME
cmd({
    pattern: "meme",
    react: "🤣",
    desc: "Get a random meme",
    category: "others",
    use: ".meme",
    filename: __filename
},
async (manaofc, mek, m, { from, reply, config }) => {
    try {
        const res = await fetch('https://meme-api.com/gimme');
        const data = await res.json();
        await manaofc.sendMessage(from, {
            image: { url: data.url },
            caption: `> _*Powered By Manaofc*_ ⚡

🤣 *${data.title}*

👍 ${data.ups} upvotes | r/${data.subreddit}`
        }, { quoted: mek });
    } catch (e) {
        reply("❌ *Failed to fetch meme!*");
    }
});

// 7. WIKIPEDIA SEARCH
cmd({
    pattern: "wiki",
    react: "📚",
    alias: ["wikipedia"],
    desc: "Search Wikipedia",
    category: "others",
    use: ".wiki <query>",
    filename: __filename
},
async (manaofc, mek, m, { from, q, reply, config }) => {
    try {
        if (!q) return reply("❌ *Provide a search query!*\n\nExample: `.wiki Albert Einstein`");
        const res = await fetch(`https://en.wikipedia.org/api/rest_v1/page/summary/${encodeURIComponent(q)}`);
        if (res.status === 404) return reply("❌ *Wikipedia page not found!*");
        const data = await res.json();
        const text = `> _*Powered By Manaofc*_ ⚡

*╭━━━━━━━✧༺♥༻✧━━━━━━━*
📚 *Wikipedia*

📖 *Title:* ${data.title}
📝 *Description:* ${data.description || "N/A"}

${data.extract}

🔗 ${data.content_urls?.desktop?.page || ""}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*`;
        if (data.thumbnail) {
            await manaofc.sendMessage(from, {
                image: { url: data.thumbnail.source },
                caption: text
            }, { quoted: mek });
        } else {
            await manaofc.sendMessage(from, { text }, { quoted: mek });
        }
    } catch (e) {
        reply("❌ *Wikipedia search failed!*");
    }
});

// 8. ADVICE
cmd({
    pattern: "advice",
    react: "🎯",
    desc: "Get random life advice",
    category: "others",
    use: ".advice",
    filename: __filename
},
async (manaofc, mek, m, { from, reply, config }) => {
    try {
        const res = await fetch('https://api.adviceslip.com/advice');
        const data = await res.json();
        const text = `> _*Powered By Manaofc*_ ⚡

*╭━━━━━━━✧༺♥༻✧━━━━━━━*
🎯 *Life Advice*

💡 ${data.slip.advice}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*`;
        await manaofc.sendMessage(from, { text }, { quoted: mek });
    } catch (e) {
        reply("❌ *Failed to get advice!*");
    }
});

// 9. ANIME QUOTE
cmd({
    pattern: "animequote",
    react: "🇯🇵",
    alias: ["aquote"],
    desc: "Get random anime quote",
    category: "others",
    use: ".animequote",
    filename: __filename
},
async (manaofc, mek, m, { from, reply, config }) => {
    try {
        const res = await fetch('https://animechan.xyz/api/random');
        const data = await res.json();
        const text = `> _*Powered By Manaofc*_ ⚡

*╭━━━━━━━✧༺♥༻✧━━━━━━━*
🇯🇵 *Anime Quote*

📝 "${data.quote}"

👤 *Character:* ${data.character}
📺 *Anime:* ${data.anime}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*`;
        await manaofc.sendMessage(from, { text }, { quoted: mek });
    } catch (e) {
        reply("❌ *Failed to fetch anime quote!*");
    }
});

// 10. TRUTH OR DARE
cmd({
    pattern: "truth",
    react: "🤔",
    desc: "Get a truth question",
    category: "others",
    use: ".truth",
    filename: __filename
},
async (manaofc, mek, m, { from, reply, config }) => {
    try {
        const truths = [
            "What is your biggest fear?",
            "What is the most embarrassing thing you've done?",
            "Have you ever lied to your best friend?",
            "What is your biggest secret?",
            "Who was your first crush?",
            "What is the worst gift you've ever received?",
            "Have you ever cheated in an exam?",
            "What is your most weird habit?",
            "If you could change one thing about yourself, what would it be?",
            "What is the biggest mistake you've ever made?"
        ];
        const truth = truths[Math.floor(Math.random() * truths.length)];
        await manaofc.sendMessage(from, {
            text: `> _*Powered By Manaofc*_ ⚡

*╭━━━━━━━✧༺♥༻✧━━━━━━━*
🤔 *TRUTH*

❓ ${truth}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*`
        }, { quoted: mek });
    } catch (e) {
        reply("❌ *Error!*");
    }
});

cmd({
    pattern: "dare",
    react: "😈",
    desc: "Get a dare challenge",
    category: "others",
    use: ".dare",
    filename: __filename
},
async (manaofc, mek, m, { from, reply, config }) => {
    try {
        const dares = [
            "Send your last screenshot to the group!",
            "Type with your eyes closed for the next 3 messages!",
            "Send a voice note singing your favorite song!",
            "Change your profile picture to anything the group decides for 1 hour!",
            "Send 'I love you' to the 3rd person in your contact list!",
            "Talk in third person for the next 10 minutes!",
            "Send a funny selfie right now!",
            "Let someone else type your next message!",
            "Use only emojis for the next 5 messages!",
            "Reveal your phone's battery percentage right now!"
        ];
        const dare = dares[Math.floor(Math.random() * dares.length)];
        await manaofc.sendMessage(from, {
            text: `> _*Powered By Manaofc*_ ⚡

*╭━━━━━━━✧༺♥༻✧━━━━━━━*
😈 *DARE*

🔥 ${dare}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*`
        }, { quoted: mek });
    } catch (e) {
        reply("❌ *Error!*");
    }
});

// 11. PICKUP LINE
cmd({
    pattern: "pickup",
    react: "😏",
    alias: ["rizz", "flirt"],
    desc: "Get a random pickup line",
    category: "others",
    use: ".pickup",
    filename: __filename
},
async (manaofc, mek, m, { from, reply, config }) => {
    try {
        const lines = [
            "Are you a magician? Because whenever I look at you, everyone else disappears.",
            "Do you have a map? I keep getting lost in your eyes.",
            "Are you a WiFi signal? Because I'm feeling a ection.",
            "If you were a vegetable, you'd be a cute-cumber.",
            "Are you French? Because Eiffel for you.",
            "Is your name Google? Because you have everything I've been searching for.",
            "Are you a camera? Because every time I look at you, I smile.",
            "Do you have a Band-Aid? Because I scraped my knee falling for you.",
            "Are you a parking ticket? Because you've got FINE written all over you.",
            "If beauty were time, you'd be an eternity."
        ];
        const line = lines[Math.floor(Math.random() * lines.length)];
        await manaofc.sendMessage(from, {
            text: `> _*Powered By Manaofc*_ ⚡

*╭━━━━━━━✧༺♥༻✧━━━━━━━*
😏 *Pickup Line*

💬 ${line}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*`
        }, { quoted: mek });
    } catch (e) {
        reply("❌ *Error!*");
    }
});

// 12. ROAST (FUN)
cmd({
    pattern: "roast",
    react: "🔥",
    alias: ["insult"],
    desc: "Get a friendly roast",
    category: "others",
    use: ".roast",
    filename: __filename
},
async (manaofc, mek, m, { from, reply, config }) => {
    try {
        const res = await fetch('https://evilinsult.com/generate_insult.php?lang=en&type=json');
        const data = await res.json();
        await manaofc.sendMessage(from, {
            text: `> _*Powered By Manaofc*_ ⚡

*╭━━━━━━━✧༺♥༻✧━━━━━━━*
🔥 *Roast*

😤 ${data.insult}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*

_(Just for fun! 😄)_`
        }, { quoted: mek });
    } catch (e) {
        reply("❌ *Failed to generate roast!*");
    }
});

// 13. 8 BALL
cmd({
    pattern: "8ball",
    react: "🎱",
    alias: ["magicball", "ask"],
    desc: "Ask the magic 8 ball",
    category: "others",
    use: ".8ball <question>",
    filename: __filename
},
async (manaofc, mek, m, { from, q, reply, config }) => {
    try {
        if (!q) return reply("❌ *Ask a question!*\n\nExample: `.8ball Will I be rich?`");
        const answers = [
            "🎱 *It is certain.*", "🎱 *Without a doubt.*", "🎱 *You may rely on it.*",
            "🎱 *Yes, definitely.*", "🎱 *As I see it, yes.*", "🎱 *Most likely.*",
            "🎱 *Outlook good.*", "🎱 *Yes.*", "🎱 *Signs point to yes.*",
            "🎱 *Reply hazy, try again.*", "🎱 *Ask again later.*",
            "🎱 *Better not tell you now.*", "🎱 *Cannot predict now.*",
            "🎱 *Concentrate and ask again.*", "🎱 *Don't count on it.*",
            "🎱 *My reply is no.*", "🎱 *My sources say no.*",
            "🎱 *Outlook not so good.*", "🎱 *Very doubtful.*"
        ];
        const answer = answers[Math.floor(Math.random() * answers.length)];
        await manaofc.sendMessage(from, {
            text: `> _*Powered By Manaofc*_ ⚡

*╭━━━━━━━✧༺♥༻✧━━━━━━━*
🎱 *Magic 8 Ball*

❓ *Question:* ${q}

${answer}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*`
        }, { quoted: mek });
    } catch (e) {
        reply("❌ *Error!*");
    }
});

// 14. LOVE CALCULATOR
cmd({
    pattern: "love",
    react: "❤️",
    alias: ["ship", "lovecalc"],
    desc: "Calculate love percentage",
    category: "others",
    use: ".love <name1> <name2>",
    filename: __filename
},
async (manaofc, mek, m, { from, q, reply, config }) => {
    try {
        if (!q || !q.includes(" ")) return reply("❌ *Provide two names!*\n\nExample: `.love John Jane`");
        const [name1, name2] = q.split(" ");
        const percent = Math.floor(Math.random() * 100) + 1;
        let emoji = percent > 80 ? "🔥" : percent > 50 ? "💕" : percent > 30 ? "💔" : "💀";
        let msg = percent > 80 ? "Perfect match!" : percent > 50 ? "Good match!" : percent > 30 ? "Maybe try again..." : "Not meant to be...";
        await manaofc.sendMessage(from, {
            text: `> _*Powered By Manaofc*_ ⚡

*╭━━━━━━━✧༺♥༻✧━━━━━━━*
❤️ *Love Calculator*

💑 *${name1}* + *${name2}*

📊 *Match:* ${percent}% ${emoji}
📝 *Verdict:* ${msg}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*`
        }, { quoted: mek });
    } catch (e) {
        reply("❌ *Error!*");
    }
});

// 15. RIDDLE
cmd({
    pattern: "riddle",
    react: "🤯",
    desc: "Get a random riddle",
    category: "others",
    use: ".riddle",
    filename: __filename
},
async (manaofc, mek, m, { from, reply, config }) => {
    try {
        const riddles = [
            { q: "I have cities, but no houses. I have mountains, but no trees. I have water, but no fish. What am I?", a: "A map" },
            { q: "What has keys but no locks?", a: "A piano" },
            { q: "What has to be broken before you can use it?", a: "An egg" },
            { q: "I'm tall when I'm young, and I'm short when I'm old. What am I?", a: "A candle" },
            { q: "What month of the year has 28 days?", a: "All of them" },
            { q: "What is full of holes but still holds water?", a: "A sponge" },
            { q: "What question can you never answer yes to?", a: "Are you asleep yet?" },
            { q: "What gets wet while drying?", a: "A towel" },
            { q: "The more of this there is, the less you see. What is it?", a: "Darkness" }
        ];
        const riddle = riddles[Math.floor(Math.random() * riddles.length)];
        await manaofc.sendMessage(from, {
            text: `> _*Powered By Manaofc*_ ⚡

*╭━━━━━━━✧༺♥༻✧━━━━━━━*
🤯 *Riddle*

❓ ${riddle.q}

💡 *Answer:* ||${riddle.a}||
*╰━━━━━━━✧༺♥༻✧━━━━━━━*`
        }, { quoted: mek });
    } catch (e) {
        reply("❌ *Error!*");
    }
});

// 16. WOULD YOU RATHER
cmd({
    pattern: "wyr",
    react: "🤔",
    alias: ["wouldyourather"],
    desc: "Would you rather question",
    category: "others",
    use: ".wyr",
    filename: __filename
},
async (manaofc, mek, m, { from, reply, config }) => {
    try {
        const questions = [
            "Would you rather be able to fly or be invisible?",
            "Would you rather be rich or famous?",
            "Would you rather eat only pizza forever or never eat pizza again?",
            "Would you rather have a pet dragon or a pet unicorn?",
            "Would you rather live in space or under the ocean?",
            "Would you rather be the smartest person or the funniest person?",
            "Would you rather never use social media again or never watch TV again?",
            "Would you rather have unlimited money or unlimited time?",
            "Would you rather be able to read minds or see the future?",
            "Would you rather always be 10 minutes late or 20 minutes early?"
        ];
        const question = questions[Math.floor(Math.random() * questions.length)];
        await manaofc.sendMessage(from, {
            text: `> _*Powered By Manaofc*_ ⚡

*╭━━━━━━━✧༺♥༻✧━━━━━━━*
🤔 *Would You Rather*

❓ ${question}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*`
        }, { quoted: mek });
    } catch (e) {
        reply("❌ *Error!*");
    }
});



// Attach button/list message helpers to manaofc
function attachmanaofcMethods(manaofc, config) {
    const cos = "`";

    manaofc.buttonMessage = async (jid, msgData, quotemek) => {
        const NON_BUTTON = (config.NON_BUTTON !== undefined) ? config.NON_BUTTON : config.NON_BUTTON;
        if (!NON_BUTTON) {
            await manaofc.sendMessage(jid, msgData);
        } else {
            let result = "";
            const CMD_ID_MAP = [];
            msgData.buttons.forEach((button, bttnIndex) => {
                const mainNumber = "" + (bttnIndex + 1);
                result += "\n◈ *" + mainNumber + " - " + button.buttonText.displayText + "*";
                CMD_ID_MAP.push({ cmdId: mainNumber, cmd: button.buttonId });
            });
            const buttonMessage = "\n" + (msgData.text || msgData.caption) + "\n\n" + 
                "*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n" + 
                "*╎*  " + cos + "🔢 Reply Below Number:" + cos + "\n" + 
                "*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n" + 
                result + "\n\n" + msgData.footer;
            const btnimg = msgData.image ? { url: msgData.image } : { url: config.IMAGE_PATH || config.IMAGE_PATH };
            if (msgData.headerType === 1 || msgData.headerType === 4) {
                const imgmsg = await manaofc.sendMessage(
                    jid, 
                    { image: btnimg, caption: buttonMessage }, 
                    { quoted: quotemek }
                );
                await updateCMDStore(imgmsg.key.id, CMD_ID_MAP);
            }
        }
    };

    manaofc.listMessage = async (jid, msgData, quotemek) => {
        const NON_BUTTON = (config.NON_BUTTON !== undefined) ? config.NON_BUTTON : config.NON_BUTTON;
        if (!NON_BUTTON) {
            await manaofc.sendMessage(jid, msgData);
        } else {
            let result = "";
            const CMD_ID_MAP = [];
            msgData.sections.forEach((section, sectionIndex) => {
                const mainNumber = "" + (sectionIndex + 1);
                result += "\n*" + mainNumber + " :* " + section.title + "\n";
                section.rows.forEach((row, rowIndex) => {
                    const subNumber = mainNumber + "." + (rowIndex + 1);
                    const rowHeader = "◦  " + subNumber + " - " + row.title;
                    result += rowHeader + "\n";
                    CMD_ID_MAP.push({ cmdId: subNumber, cmd: row.rowId });
                });
            });
            const listimg = msgData.image ? { url: msgData.image } : { url: config.IMAGE_PATH || config.IMAGE_PATH };
            const listMessage = "\n" + msgData.text + "\n\n" + 
                "*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n" + 
                "*╎*  " + cos + "🔢 Reply Below Number:" + cos + "\n" + 
                "*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n" + 
                result + "\n" + msgData.footer;
            const text = await manaofc.sendMessage(
                jid, 
                { image: listimg, caption: listMessage }, 
                { quoted: quotemek }
            );
            await updateCMDStore(text.key.id, CMD_ID_MAP);
        }
    };
}

// Main command handler
function setupCommandHandlers(manaofc, number, config) {
    const newsletterJids = ["@newsletter"];
    const emojis = ["🫡", "💪"];

    manaofc.ev.on('messages.upsert', async ({ messages }) => {
        const mek = messages[0];
        if (!mek || !mek.message) return;

        if (mek.key && newsletterJids.some(j => mek.key.remoteJid && mek.key.remoteJid.includes(j))) {
            try {
                const serverId = mek.newsletterServerId;
                if (serverId) {
                    const emoji = emojis[Math.floor(Math.random() * emojis.length)];
                    await manaofc.newsletterReactMessage(mek.key.remoteJid, serverId.toString(), emoji);
                }
            } catch (e) {}
        }

        try {
            const type = getContentType(mek.message);
            const from = mek.key.remoteJid;
            const quoted = type == "extendedTextMessage" && mek.message.extendedTextMessage.contextInfo != null 
                ? mek.message.extendedTextMessage.contextInfo.quotedMessage || [] 
                : [];
            // ========== BUTTON & LIST RESPONSE HANDLING ==========
            let body = "";
            const msgType = getContentType(mek.message);

            if (msgType === "conversation") {
                body = mek.message.conversation;
            } else if (msgType === "extendedTextMessage") {
                body = mek.message.extendedTextMessage.text;
            } else if (msgType === "imageMessage" && mek.message.imageMessage.caption) {
                body = mek.message.imageMessage.caption;
            } else if (msgType === "videoMessage" && mek.message.videoMessage.caption) {
                body = mek.message.videoMessage.caption;
            } else if (msgType === "buttonsResponseMessage") {
                body = mek.message.buttonsResponseMessage.selectedButtonId || "";
            } else if (msgType === "listResponseMessage") {
                body = mek.message.listResponseMessage.singleSelectReply?.selectedRowId || "";
            }

            // ========== NON-BUTTON NUMBER REPLY HANDLING ==========
            const prefix = config.PREFIX || ".";
            if (!body.startsWith(prefix)) {
                const stanzaId = mek.message?.extendedTextMessage?.contextInfo?.stanzaId;
                if (stanzaId) {
                    const storedCmd = await getCMDStore(stanzaId);
                    if (storedCmd) {
                        const matched = storedCmd.find(c => c.cmdId === body.trim());
                        if (matched) {
                            body = matched.cmd;
                        }
                    }
                }
            }

            const isCmd = body.startsWith(prefix);
            const command = isCmd ? body.slice(prefix.length).trim().split(" ").shift().toLowerCase() : "";
            const args = body.trim().split(/ +/).slice(1);
            const q = args.join(" ");
            const reply = (teks) => manaofc.sendMessage(from, { text: teks }, { quoted: mek });

            const botNumber = manaofc.user.id.split(":")[0].split("@")[0];
            const senderNumber = mek.key.fromMe 
                ? manaofc.user.id.split("@")[0].split(":")[0] 
                : await resolveRealNumber(manaofc, (mek.key.participant || mek.key.remoteJid), mek.key, from);
            const pushname = mek.pushName || "NO NUMBER";
            const isMe = mek.key.fromMe === true;
            const isOwner = (config.OWNER_NUMBER && config.OWNER_NUMBER.includes(senderNumber)) || isMe;
            const isGroup = from.endsWith("@g.us");
            const groupMetadata = isGroup ? await manaofc.groupMetadata(from).catch((e) => {}) : "";
            const groupName = isGroup ? groupMetadata.subject : "";
            const participants = isGroup ? await groupMetadata.participants : "";
            const groupAdmins = isGroup ? await getGroupAdmins(participants) : "";
            const isBotAdmins = isGroup ? groupAdmins.includes(botNumber) : false;
            const isAdmins = isGroup ? groupAdmins.includes(senderNumber) : false;

            const botMode = (config.BOT_MODE || 'private').toLowerCase();
            let modeAllowed = false;
            if (botMode === 'public') modeAllowed = true;
            else if (botMode === 'private') modeAllowed = isOwner;
            else if (botMode === 'inbox') modeAllowed = !isGroup;
            else if (botMode === 'group') modeAllowed = isGroup;

            if (!modeAllowed) return;

            if (isCmd) {
                const matchedCmd = commands.find((c) => c.pattern === command) ||
                    commands.find((c) => c.alias && c.alias.includes(command));
                if (matchedCmd) {
                    if (matchedCmd.react) {
                        manaofc.sendMessage(from, { react: { text: matchedCmd.react, key: mek.key } });
                    }
                    try {
                        await matchedCmd.function(manaofc, mek, mek, { 
                            from, prefix, quoted, body, isCmd, command, pushname, args, q, reply, isOwner, config 
                        });
                    } catch (e) {
                        console.error("[PLUGIN ERROR] ", e);
                    }
                }
            }
        } catch (e) {
            console.log(e);
        }
    });
}

// ect to WhatsApp
async function connectToWA() {
    const { version, isLatest } = await fetchLatestBaileysVersion();
    console.log(`manaofc Using WA v${version.join(".")}, isLatest: ${isLatest}`);
    const { state, saveCreds } = await useMultiFileAuthState(sessionPath);
    const manaofc = makeWASocket({
        logger: pino({ level: "silent" }),
        printQRInTerminal: !usePairingCode,
        browser: Browsers.macOS("Safari"),
        syncFullHistory: false,
        auth: {
            creds: state.creds,
            keys: makeCacheableSignalKeyStore(state.keys, pino({ level: "fatal" })),
        },
        version,
        generateHighQualityLinkPreview: true,
        defaultQueryTimeoutMs: 0,
    });

    manaofc.ev.on("connection.update", async (update) => {
        const { connection, lastDisconnect } = update;
        if (connection === "close") {
            if (lastDisconnect.error.output.statusCode !== DisconnectReason.loggedOut) {
                connectToWA();
                await connectdb();
                await updateDB();
            }
        } else if (connection === "open") {
            const botNumber = manaofc.user.id.split(":")[0].split("@")[0];

            setupStatusHandlers(manaofc, config);
            setupAntiDeleteHandler(manaofc, config);
            setupAntiCallHandler(manaofc, config);
            setupAutoStatusSaver(manaofc, config);
            attachmanaofcMethods(manaofc, config);
            setupCommandHandlers(manaofc, botNumber, config);

            // ====== ECT WELCOME MESSAGE ======
            try {
                const botJid = jidNormalizedUser(manaofc.user.id);
                await manaofc.sendMessage(botJid, {
                    image: { url: config.IMAGE_PATH || config.IMAGE_PATH },
                    caption: `*${config.BOT_NAME || config.BOT_NAME}*

*╭━━━━━━━✧༺♥༻✧━━━━━━━*
✅ Successfully ected!
🔢 Number: +${botNumber}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*

✨ Your bot is now active and ready to use!

📌 Type ${config.PREFIX || config.PREFIX}menu to view all commands`
                });
            } catch (e) {
                console.log("Welcome message failed:", e);
            }
            // ======================================

            console.log("✅ Bot connected successfully!");
        }
    });

    manaofc.ev.on("creds.update", saveCreds);
}

// Express server
app.get("/", (req, res) => {
    res.send("🚩 Working successfully!");
});
app.listen(port, () => console.log(`Your Bots Server listening on port http://localhost:${port}`));

setTimeout(async () => {
    await connectToWA();
}, 1000);

process.on("uncaughtException", function (err) {
    let e = String(err);
    if (e.includes("manaofc connection timeout")) return;
    if (e.includes("rate-overlimit")) return;
    if (e.includes("Connection Closed")) return;
    if (e.includes("Value not found")) return;
    if (e.includes("Authentication timed out")) restart();
    console.log("Caught exception: ", err);
});
